{-# LANGUAGE MultiWayIf #-}
module Instructions where

import Data.Binary.Get
import Data.Bits
import Data.Word (Word16, Word8)
import Numeric (showHex)

newtype Address =
  Address Word16 deriving (Eq, Ord)

instance Show Address where
  showsPrec _ (Address w16) =
    showHex w16

newtype Register =
  Register Word8 deriving (Eq)

instance Show Register where
  showsPrec _ (Register w8) =
    ("V" ++) . showHex w8

data Instruction =
  InstSys !Address |
  InstClr |
  InstRts |
  InstJump !Address |
  InstCall !Address |
  InstSke !Register !Word8 |
  InstSkne !Register !Word8 |
  InstSkre !Register !Register |
  InstLoad !Register !Word8 |
  InstAdd !Register !Word8 |
  InstMove !Register !Register |
  InstOr !Register !Register |
  InstAnd !Register !Register |
  InstXor !Register !Register |
  InstAddr !Register !Register |
  InstSub !Register !Register |
  InstShr !Register !Register |
  InstShl !Register !Register |
  InstSkrne !Register !Register |
  InstLoadI !Address |
  InstJumpI !Address |
  InstRand !Register !Word8 |
  InstDraw !Register !Register !Word8 |
  InstSkpr !Register |
  InstSkup !Register |
  InstMoveD !Register |
  InstKeyD !Register |
  InstLoadD !Register |
  InstLoadS !Register |
  InstAddI !Register |
  InstLdspr !Register |
  InstBcd !Register |
  InstStor !Register |
  InstRead !Register
  deriving (Eq, Show)

parseInstruction :: Get Instruction
parseInstruction = do
  b0 <- getWord8
  b1 <- getWord8
  let addr =
        Address n3
      reg1 =
        Register (b0 .&. 0xF)
      reg2 =
        Register ((b1 .&. 0xF0) .>>. 4)
      n1 :: Word8 =
        b1 .&. 0xF
      n2 :: Word8 =
        b1
      n3 :: Word16 =
        ((fromIntegral b0 .&. 0xF) .<<. 8) .|. fromIntegral b1
  case (b0 .&. 0xF0) .>>. 4 of
    0x0 -> if
      | b0 == 0 && b1 == 0xE0 -> pure InstClr
      | b0 == 0 && b1 == 0xEE -> pure InstRts
      | otherwise -> pure $ InstSys addr
    0x1 -> pure $ InstJump addr
    0x2 -> pure $ InstCall addr
    0x3 -> pure $ InstSke reg1 n2
    0x4 -> pure $ InstSkne reg1 n2
    0x5 -> pure $ InstSkre reg1 reg2
    0x6 -> pure $ InstLoad reg1 n2
    0x7 -> pure $ InstAdd reg1 n2
    0x8 -> case b1 .&. 0xF of
      0x0 -> pure $ InstMove reg1 reg2
      0x1 -> pure $ InstOr reg1 reg2
      0x2 -> pure $ InstAnd reg1 reg2
      0x3 -> pure $ InstXor reg1 reg2
      0x4 -> pure $ InstAddr reg1 reg2
      0x5 -> pure $ InstSub reg1 reg2
      0x6 -> pure $ InstShr reg1 reg2
      0xE -> pure $ InstShl reg1 reg2
      _ -> fail "Invalid instruction"
    0x9 -> pure $ InstSkrne reg1 reg2
    0xA -> pure $ InstLoadI addr
    0xB -> pure $ InstJumpI addr
    0xC -> pure $ InstRand reg1 n2
    0xD -> pure $ InstDraw reg1 reg2 n1
    0xE -> case b1 of
      0x9E -> pure $ InstSkpr reg1
      0xA1 -> pure $ InstSkup reg1
      _ -> fail "Invalid instruction"
    0xF -> case b1 of
      0x07 -> pure $ InstMoveD reg1
      0x0A -> pure $ InstKeyD reg1
      0x15 -> pure $ InstLoadD reg1
      0x18 -> pure $ InstLoadS reg1
      0x1E -> pure $ InstAddI reg1
      0x29 -> pure $ InstLdspr reg1
      0x33 -> pure $ InstBcd reg1
      0x55 -> pure $ InstStor reg1
      0x65 -> pure $ InstRead reg1
      _ -> fail "Invalid instruction"
    _ -> fail "Impossible"
