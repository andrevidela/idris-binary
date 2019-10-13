
module Binary

import Data.Vect

%default total

data Bit = O | I

-- L for little endian, B for Big endian
-- Little endian end with the least significant bit.
-- Big endian ends with the most significant bit.
data Endian = L | B

reversed : Endian -> Endian
reversed L = B
reversed B = L

Eq Bit where
  O == O = True
  I == I = True
  _ == _ = False

data BitVect : (n : Nat) -> Endian -> Type where
  LittleEndianVect : Vect n Bit -> BitVect n L
  BigEndianVect : Vect n Bit -> BitVect n B

map : (Bit -> Bit) -> BitVect n e -> BitVect n e
map f (LittleEndianVect xs) = LittleEndianVect $ map f xs
map f (BigEndianVect xs) = BigEndianVect $ map f xs

flip : Bit -> Bit
flip O = I
flip I = O

-- add two bits and return (Sum, Carry)
addBits : Bit -> Bit -> (Bit, Bit)
addBits O O = (O, O)
addBits O I = (I, O)
addBits I O = (I, O)
addBits I I = (I, I)

||| Add three bits together and return (Sum, Carry)
addBits3 : Bit -> Bit -> Bit -> (Bit, Bit)
addBits3 O O O = (O, O)
addBits3 O O I = (I, O)
addBits3 O I O = (I, O)
addBits3 I O O = (I, O)
addBits3 O I I = (O, I)
addBits3 I O I = (O, I)
addBits3 I I O = (O, I)
addBits3 I I I = (I, I)


bitSumCommutative : {b1, b2 : Bit} -> b1 `addBits` b2 = b2 `addBits` b1
bitSumCommutative {b1 = O} {b2 = O} = Refl
bitSumCommutative {b1 = O} {b2 = I} = Refl
bitSumCommutative {b1 = I} {b2 = O} = Refl
bitSumCommutative {b1 = I} {b2 = I} = Refl


Ictet : Type
Ictet = Vect 8 Bit

negation : BitVect n e -> BitVect n e
negation = map flip

reverse : BitVect n b -> BitVect n (reversed b)
reverse (LittleEndianVect xs) = BigEndianVect $ reverse xs
reverse (BigEndianVect xs) = LittleEndianVect $ reverse xs


||| Addition with LSB
additionLSB : BitVect n B -> BitVect n B -> BitVect (S n) B
additionLSB (BigEndianVect x) (BigEndianVect y) = BigEndianVect $ addWithCarry x y O
  where
    addWithCarry : Vect n Bit -> Vect n Bit -> Bit -> Vect (S n) Bit
    addWithCarry [] [] z = [z]
    addWithCarry (x :: xs) (y :: ys) z = let (s, c) = addBits3 x y z in s :: addWithCarry xs ys c

||| Addition MSB
additionMSB : BitVect n L -> BitVect n L -> BitVect (S n) L
additionMSB x y = reverse (additionLSB (reverse x) (reverse y))

addition : BitVect n e -> BitVect n e -> BitVect (S n) e
addition {e = L} x y = additionMSB x y
addition {e = B} x y = additionLSB x y

