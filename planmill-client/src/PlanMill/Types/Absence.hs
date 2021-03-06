{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
-- |
-- Copyright : (c) 2015 Futurice Oy
-- License   : BSD3
-- Maintainer: Oleg Grenrus <oleg.grenrus@iki.fi>
module PlanMill.Types.Absence (Absence(..), Absences, AbsenceId) where

import PlanMill.Internal.Prelude

import PlanMill.Types.Identifier (HasIdentifier (..), Identifier)
import PlanMill.Types.Project    (ProjectId)
import PlanMill.Types.User       (UserId)

type AbsenceId = Identifier Absence
type Absences = Vector Absence

data Absence = Absence
    { _absenceId              :: !AbsenceId
    , absencePerson           :: !UserId
    , absenceProject          :: !ProjectId
    , absenceAccepterPerson   :: !UserId
    , absenceInterruptionDate :: !(Maybe UTCTime)
    , absenceCreated          :: !(Maybe UTCTime)
    , absenceStart            :: !Day
    , absenceDescription      :: !(Maybe Text)
    , absenceVacationYear     :: !(Maybe Int)
    , absenceVacationLength   :: !Int
    , absenceAbsenceType      :: !Int  -- TODO
    , absenceModified         :: !(Maybe UTCTime)
    , absenceFinish           :: !Day
    , absenceSubstitutePerson :: !(Maybe UserId)
    , absenceStatus           :: !Int  -- TODO
    }
    deriving (Eq, Ord, Show, Read, Generic, Typeable)

makeLenses ''Absence
deriveGeneric ''Absence

instance Hashable Absence
instance NFData Absence
instance AnsiPretty Absence
instance Binary Absence
instance HasStructuralInfo Absence where structuralInfo = sopStructuralInfo
instance HasSemanticVersion Absence

instance HasIdentifier Absence Absence where
    identifier = absenceId

instance FromJSON Absence where
    parseJSON = withObject "Absence" $ \obj ->
        Absence <$> obj .: "id"
                <*> obj .: "person"
                <*> obj .: "project"
                <*> obj .: "accepterPerson"
                -- TODO: I'd add a combinator to aeson-extra to make this prettier
                <*> (getU <$$> obj .:? "interruptionDate")
                <*> (getU <$$> obj .:? "created")
                <*> (dayFromZ <$> obj .: "start")
                <*> obj .: "description"
                <*> obj .: "vacationYear"
                <*> obj .: "vacationLength"
                <*> obj .: "absenceType"
                <*> (getU <$$> obj .:? "modified")
                <*> (dayFromZ <$> obj .: "finish")
                <*> obj .: "substitutePerson"
                <*> obj .: "status"
