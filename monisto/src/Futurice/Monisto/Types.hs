{-# LANGUAGE FlexibleContexts, FlexibleInstances, StandaloneDeriving, MultiParamTypeClasses, UndecidableInstances #-}
-- |
--
module Futurice.Monisto.Types (
    -- * Schema
    -- | Schemas have kind @[('Symbol', [('Symbol', *)]@

    -- ** Entities
    EntityType,
    mkEntityType,
    ValidEntity,
    -- ** Attributes
    Attribute,
    mkTextAttribute,
    ValidAttribute,
    
    -- * Database
    Database,
    emptyDatabase,

    -- ** Entity identifiers
    EntityId,
    mkEntityId,
    -- ** Facts
    Fact,
    mkFact,
    applyFact,

    -- * Selecting
    NP(..),
    Value(..),
    selectById,
    selectById',
    ) where

import Futurice.Prelude

import GHC.TypeLits (Symbol, KnownSymbol, symbolVal)
import Data.Dependent.Map (DMap, GOrdering(..))
import Data.Type.Equality
import Data.Type.Bool
import Data.GADT.Compare (GEq (..))
import Data.GADT.Show (GShow(..))
import Data.Dependent.Sum (ShowTag(..))
import Generics.SOP (NP(..), K(..), I(..), All, hcmap, hsequence', hpure, type (:.:) (..))

import Unsafe.Coerce (unsafeCoerce)

import qualified Data.Dependent.Map as DMap
import qualified Generics.SOP as SOP

-------------------------------------------------------------------------------
-- Schema
-------------------------------------------------------------------------------

-- | 'EntityType' is roughly what tables are in SQL databases.
-- Values act as a 'Proxy', also carrying a bit of proof witnesses with it.
data EntityType (schema :: [(Symbol, [(Symbol, *)])]) (entityName :: Symbol) = EntityType

-- | Create 'EntityType'
mkEntityType
    :: ValidEntity schema entityType
    => EntityType schema entityType
mkEntityType = EntityType

data Attribute
    (schema :: [(Symbol, [(Symbol, *)])])
    (ent ::  Symbol)
    (attr :: (Symbol, *))
  where
    AText
        :: ValidAttribute schema ent '(name, Text)
        => Proxy ent
        -> Proxy name
        -> Attribute schema ent '(name, Text)
    -- ARef  :: KnownSymbol name => Attribute '(name, reference)

instance GEq (Attribute schema ent) where
    geq (AText a a') (AText b b') = case (eqSymbols a b, eqSymbols a' b') of
        (Just Refl, Just Refl) -> Just Refl
        _                      -> Nothing

instance DMap.GCompare (Attribute schema ent) where
    gcompare (AText a a') (AText b b') = case (eqSymbols a b, eqSymbols a' b') of
        (Just Refl, Just Refl) -> GEQ
        _                      ->
            case compare (symbolVal a) (symbolVal b) <> compare (symbolVal a') (symbolVal b') of
                LT -> GLT
                _  -> GGT

instance GShow (Attribute schema ent) where
    gshowsPrec _ (AText _ _) = showString "AText"

mkTextAttribute
    :: (ValidAttribute schema ent '(attrName, Text), KnownSymbol attrName)
    => Attribute schema ent '(attrName, Text)
mkTextAttribute = AText Proxy Proxy

-------------------------------------------------------------------------------
-- Singleton schema
-------------------------------------------------------------------------------

class KnownSymbol (AttrName attr) => IAttribute
    (schema :: [(Symbol, [(Symbol, *)])])
    (ent ::  Symbol)
    (attr :: (Symbol, *)) where
    iattribute :: Proxy attr -> Attribute schema ent attr

instance ValidAttribute schema ent '(sym, Text) => IAttribute schema ent '(sym, Text) where
    iattribute _ = AText Proxy Proxy

-------------------------------------------------------------------------------
-- Values
-------------------------------------------------------------------------------

-- | The type representing database.
newtype Database (schema :: [(Symbol, [(Symbol, *)])]) =
    MkDatabase (DMap (EntityId schema) (Entity schema))

-- | Empty 'Database'
emptyDatabase :: Database schema
emptyDatabase = MkDatabase DMap.empty

instance ShowTag (EntityId schema) (Entity schema) where
    showTaggedPrec (EntityId _ _) d (MkEntity e) = showsPrec d e

instance Show (Database schema) where
    showsPrec d (MkDatabase db) = showParen (d > 11)
        $ showString "MkDatabase " 
        . showsPrec 10 (DMap.toList db)

-- EntityId
-------------------------------------------------------------------------------

-- | Entity identifier
data EntityId (schema :: [(Symbol, [(Symbol, *)])]) (ent :: Symbol) where
    EntityId
        :: (ValidEntity schema ent)
        => Proxy ent -- TODO: EntityType?
        -> Word64
      -> EntityId schema ent 

instance GEq (EntityId schema) where
    geq (EntityId pa a) (EntityId pb b) =
        if a == b
            then case eqSymbols pa pb of
                Just Refl -> Just Refl
                Nothing   -> Nothing
            else Nothing

instance DMap.GCompare (EntityId scheme) where
    gcompare (EntityId pa a) (EntityId pb b) = case compare a b of
        EQ -> case eqSymbols pa pb of
            Just Refl -> GEQ
            Nothing   -> if symbolVal pa < symbolVal pb then GLT else GGT
        LT -> GLT
        GT -> GGT

instance GShow (EntityId schema) where
    gshowsPrec d (EntityId _ eid) = showParen (d > 11)
        $ showString "EntityId "
        . showsPrec 10 eid

-- Entity
-------------------------------------------------------------------------------

data Entity schema ent where
    MkEntity
        :: ValidEntity schema ent
        => DMap (Attribute schema ent) (Value schema ent)
        -> Entity schema ent 

instance Semigroup (Entity schema ent) where
  MkEntity a <> MkEntity b = MkEntity $ DMap.union b a

-- | TODO: temporary
mkEntityId
    :: (HasEntity schema ent ~ 'True, KnownSymbol ent)
    => EntityType schema ent -> Word64 -> EntityId schema ent
mkEntityId _ = EntityId Proxy

instance ShowTag (Attribute schema ent) (Value schema ent) where
    showTaggedPrec (AText _ _) d (MkValue t) = showsPrec d t

instance Show (Entity schema ent) where
    showsPrec d (MkEntity e) = showParen (d > 11)
        $ showString "MkEntity " 
        . showsPrec 10 (DMap.toList e)

-- Value
-------------------------------------------------------------------------------

newtype Value
    (schema :: [(Symbol, [(Symbol, *)])])
    (ent :: Symbol)
    (attr :: (Symbol, *))
  = MkValue (AttrType attr)

deriving instance Show (AttrType attr) => Show (Value schema ent attr)

-------------------------------------------------------------------------------
-- Facts
-------------------------------------------------------------------------------

data Fact (schema :: [(Symbol, [(Symbol, *)])]) where
    Fact
        :: ( ValidAttribute schema ent attr )
        => EntityId schema ent
        -> Attribute schema ent attr
        -> Value schema ent attr
        -> Fact schema

instance Show (Fact schema) where
    show (Fact eid attr val) = 
        show (eid DMap.:=>  entity)
      where
        entity = MkEntity (DMap.singleton attr val)

-- | Make fact for insertion.
mkFact
    :: (ValidAttribute schema ent attr)
    => EntityId schema ent
    -> Attribute schema ent attr
    -> AttrType attr
    -> Fact schema
mkFact eid attr val = Fact eid attr (MkValue val)

-- | Insert single 'Fact' into the database.
applyFact :: forall schema. Database schema -> Fact schema -> Database schema
applyFact (MkDatabase origDb) (Fact entityId attr value) =
    MkDatabase $ applyFact' origDb entityId attr value
  where
    applyFact'
        :: forall ent attr.
           ( ValidEntity schema ent )
        => DMap (EntityId schema) (Entity schema)
        -> EntityId schema ent
        -> Attribute schema ent attr
        -> Value schema ent attr
        -> DMap (EntityId schema) (Entity schema)
    applyFact' db eid att val = DMap.insertWith (<>) eid entity db 
      where
        entity :: Entity schema ent
        entity = MkEntity (DMap.singleton att val)

-------------------------------------------------------------------------------
-- Selecting
-------------------------------------------------------------------------------

selectById
    :: forall schema ent a.
       ( All (IAttribute schema ent) (EntityFields schema ent)
       , SOP.Generic a, SOP.Code a ~ '[ MapAttrType (EntityFields schema ent) ]
       )
    => EntityId schema ent
    -> Database schema
    -> Maybe a
selectById eid db
    = SOP.to
    . SOP.SOP
    . SOP.Z
    . conv
    <$> selectById' eid db
  where

conv ::  forall schema ent fields. NP (Value schema ent) fields -> NP I (MapAttrType fields)
conv Nil = Nil
conv (x :* xs) = go' x xs
  where
    go' :: forall attr attrs. Value schema ent attr -> NP (Value schema ent) attrs -> NP I (MapAttrType (attr ': attrs))
    go' (MkValue y) ys = I y :* conv ys

selectById'
    :: All (IAttribute schema ent) (EntityFields schema ent)
    => EntityId schema ent
    -> Database schema
    -> Maybe (NP (Value schema ent) (EntityFields schema ent))
selectById' eid (MkDatabase db) = DMap.lookup eid db >>= entityToNPValue 

entityToNPValue
    :: forall schema ent.
       All (IAttribute schema ent) (EntityFields schema ent)
    => Entity schema ent
    -> Maybe (NP (Value schema ent) (EntityFields schema ent))
entityToNPValue (MkEntity e)
    = hsequence'
    $ hcmap (Proxy :: Proxy (IAttribute schema ent)) lookupField
    $ hpure (K ())
  where
    lookupField
        :: forall attr. IAttribute schema ent attr
        => K () attr -> (Maybe :.: Value schema ent) attr
    lookupField _ =
        Comp $ DMap.lookup (iattribute (Proxy :: Proxy attr)) e 

-------------------------------------------------------------------------------
-- Helpers
-------------------------------------------------------------------------------

type family AttrType (p :: (Symbol, *)) :: * where
    AttrType '(attrName, attrType) = attrType

type family MapAttrType (ps :: [(Symbol, *)]) :: [*] where
    MapAttrType '[]             = '[]
    MapAttrType (attr ': attrs) = AttrType attr  ': MapAttrType attrs

type family AttrName (p :: (Symbol, *)) :: Symbol where
    AttrName '(attrName, attrType) = attrName

type family SchemaTokens (schema :: [(Symbol, [(Symbol, *)])]) :: [Symbol] where
    SchemaTokens '[]                    = '[]
    SchemaTokens ('(name, def) ': rest) = name ': SchemaTokens rest

type family HasEntity
    (schema :: [(Symbol, [(Symbol, *)])])
    (entityName :: Symbol)
    :: Bool where
    HasEntity '[]                    entityName = 'False
    HasEntity ('(name, def) ': rest) entityName =
        name == entityName || HasEntity rest entityName

-- | Partial on purpose
type family EntityFields
    (schema :: [(Symbol, [(Symbol, *)])])
    (ent :: Symbol)
    :: [(Symbol, *)] where
    EntityFields ('(ent,  attrs) ': rest) ent = attrs
    EntityFields ('(ent', attrs) ': rest) ent = EntityFields rest ent

type family HasAttribute
    (schema :: [(Symbol, [(Symbol, *)])])
    (ent :: Symbol)
    (attr :: (Symbol, *))
    :: Bool where
    HasAttribute '[]                    entityName attr = 'False
    HasAttribute ('(name, '[]) ': rest) entityName attr =
        HasAttribute rest entityName attr 
    HasAttribute ('(name, typ ': arest) ': rest) entityName attr =
        (name == entityName && typ == attr) ||
        HasAttribute ('(name, arest) ': rest) entityName attr

-- | Entity @ent@ exists in @schema@.
type ValidEntity schema ent = (KnownSymbol ent, HasEntity schema ent ~ 'True)

-- | Attribute @ent@ exists in @schema@ in @ent@ entity 
type ValidAttribute schema ent attr =
    (ValidEntity schema ent, KnownSymbol (AttrName attr), HasAttribute schema ent attr ~'True)

eqSymbols
    :: (KnownSymbol a, KnownSymbol b)
    => Proxy a -> Proxy b -> Maybe (a :~: b)
eqSymbols a b
    | symbolVal a == symbolVal b = Just (unsafeCoerce trivialReflProof)
    | otherwise                  = Nothing

trivialReflProof :: () :~: ()
trivialReflProof = Refl 
