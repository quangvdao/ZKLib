/-
 Copyright 2023 RISC Zero, Inc.

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

import Mathlib.Data.Nat.Log

/-!
  # Helper functions for R0sy

  Most of these are simple functions that should already been in `Mathlib`.

  TODO: check if we can replace any of these with `Mathlib` versions.
-/

section Bits

def Bits.least_upper_bound (hi lo: UInt32): Nat
  := 1 <<< (1 + hi.toNat - lo.toNat)

def Bits.mask (hi lo: UInt32): UInt32
  := (Bits.least_upper_bound hi lo - 1).toUInt32 <<< lo

structure Bits (hi lo: UInt32) where
  val: UInt32 -- Fin (Bits.least_upper_bound hi lo)
  deriving BEq

def Bits.ofUInt32 (x: UInt32): Bits hi lo
  := {
    val := (x >>> lo) &&& (Bits.least_upper_bound hi lo - 1).toUInt32
  }

def Bits.toUInt32 (x: Bits hi lo): UInt32
  := x.val <<< lo

end Bits


section Hex

def charTable: Array Char
  := #[
    '0', '1', '2', '3',
    '4', '5', '6', '7',
    '8', '9', 'a', 'b',
    'c', 'd', 'e', 'f'
  ]

def UInt8.toHex (val: UInt8): String
  := Id.run do
        let lo := (val &&& 0x0f).toNat
        let hi := (val >>> 4).toNat
        let mut out: String := ""
        out := out.push charTable[hi]!
        out := out.push charTable[lo]!
        out

def UInt16.toHex (val: UInt16): String
  := Id.run do
        let lo := UInt8.toHex (val &&& 0xff).toNat.toUInt8
        let hi := UInt8.toHex (val >>> 8 &&& 0xff).toNat.toUInt8
        hi ++ lo

def UInt32.toHex (val: UInt32): String
  := Id.run do
        let lo := UInt16.toHex (val &&& 0xffff).toNat.toUInt16
        let hi := UInt16.toHex (val >>> 16 &&& 0xffff).toNat.toUInt16
        hi ++ lo

end Hex

section ByteArray

section Nat

def Nat.toUInt32Words (words: Nat) (val: Nat) (out: Array UInt32 := #[]): Array UInt32
  := match words with
      | 0 => out
      | words + 1 => Nat.toUInt32Words words (val >>> 32) (out.push (UInt32.ofNat val))

def Nat.fromUInt32Words (x: Subarray UInt32) (i: Nat := 0) (out: Nat := 0): Nat
  := if i < x.size
      then Nat.fromUInt32Words x (i + 1) ((out <<< 32) ||| UInt32.toNat x[x.size - i - 1]!)
      else out
termination_by x.size - i

end Nat

section UInt32

def UInt32.test_bit (bit: Nat) (x: UInt32): Bool
  := (1 <<< bit).toUInt32 &&& x != 0

/- Endian helpers -/

def UInt32.swap_endian (x: UInt32): UInt32 :=
  let a0 := x &&& 0xff
  let a1 := (x >>> (8*1)) &&& 0xff
  let a2 := (x >>> (8*2)) &&& 0xff
  let a3 := (x >>> (8*3)) &&& 0xff
  let c0 := a0 <<< (8*3)
  let c1 := a1 <<< (8*2)
  let c2 := a2 <<< (8*1)
  let c3 := a3
  c3 ||| c2 ||| c1 ||| c0

def UInt32.ror (x: UInt32) (n: Nat): UInt32 :=
  let l := x >>> UInt32.ofNat n
  let r := x <<< UInt32.ofNat (32 - n)
  l ||| r

def UInt32.of_be32 (b3 b2 b1 b0: UInt8): UInt32 :=
  let c0 := UInt32.ofNat (b0.val.val)
  let c1 := UInt32.ofNat (b1.val.val) <<< (8*1)
  let c2 := UInt32.ofNat (b2.val.val) <<< (8*2)
  let c3 := UInt32.ofNat (b3.val.val) <<< (8*3)
  c3 ||| c2 ||| c1 ||| c0

def UInt32.to_le (x: UInt32): ByteArray :=
  let a0 := UInt8.ofNat <| UInt32.toNat <| x &&& 0xff
  let a1 := UInt8.ofNat <| UInt32.toNat <| (x >>> (8*1)) &&& 0xff
  let a2 := UInt8.ofNat <| UInt32.toNat <| (x >>> (8*2)) &&& 0xff
  let a3 := UInt8.ofNat <| UInt32.toNat <| (x >>> (8*3)) &&& 0xff
  { data := #[ a0, a1, a2, a3 ] }

def UInt32.to_be (x: UInt32): ByteArray :=
  let a0 := UInt8.ofNat <| UInt32.toNat <| x &&& 0xff
  let a1 := UInt8.ofNat <| UInt32.toNat <| (x >>> (8*1)) &&& 0xff
  let a2 := UInt8.ofNat <| UInt32.toNat <| (x >>> (8*2)) &&& 0xff
  let a3 := UInt8.ofNat <| UInt32.toNat <| (x >>> (8*3)) &&& 0xff
  { data := #[ a3, a2, a1, a0 ] }

def UInt32.is_neg (x: UInt32): Bool
  := UInt32.test_bit 31 x

def UInt32.extend_unsigned (x: UInt32): UInt64
  := x.toNat.toUInt64

def UInt32.extend_signed (x: UInt32): UInt64
  := UInt32.extend_unsigned x ||| if UInt32.is_neg x then 0xffffffff00000000 else 0

def UInt32.neg_one: UInt32 := 0xffffffff

def UInt32.max_signed: UInt32 := 0x7fffffff

def UInt32.min_signed: UInt32 := 0x80000000

def UInt32.max_unsigned: UInt32 := 0xffffffff

def UInt32.min_unsigned: UInt32 := 0x00000000

def UInt32.toInt (x: UInt32): Int
  := if UInt32.is_neg x then Int.negOfNat (x * neg_one).toNat else x.toNat

def UInt32.lt_signed (x y: UInt32): Bool
  := UInt32.toInt x < UInt32.toInt y

def UInt32.ge_signed (x y: UInt32): Bool
  := UInt32.toInt x >= UInt32.toInt y

def UInt32.ofUInt8_signed (x: UInt8): UInt32
  := Id.run do
    let lo: Bits 7 0 := { val := x.toNat.toUInt32 }
    let hi: Bits 31 8 := Bits.ofUInt32 <| if UInt32.test_bit 7 lo.val then 0xffffffff else 0
    pure (hi.toUInt32 ||| lo.toUInt32)

def UInt32.ofUInt16_signed (x: UInt16): UInt32
  := Id.run do
    let lo: Bits 15 0 := { val := x.toNat.toUInt32 }
    let hi: Bits 31 16 := Bits.ofUInt32 <| if UInt32.test_bit 15 lo.val then 0xffffffff else 0
    pure (hi.toUInt32 ||| lo.toUInt32)

def UInt32.shr_signed (x y: UInt32): UInt32
  := Id.run do
      let lo := x >>> y
      let hi := if UInt32.is_neg x then ((1 <<< y) - 1) <<< (32 - y) else 0
      pure (hi ||| lo)

end UInt32

section UInt64

def UInt64.lo (x: UInt64): UInt32
  := x.toNat.toUInt32

def UInt64.hi (x: UInt64): UInt32
  := (x >>> 32).toNat.toUInt32

end UInt64

section ByteArray

/- Endian helpers -/

partial def ByteArray.to_be32 (x: ByteArray) (i: Nat := 0) (out: Array UInt32 := #[]): Array UInt32 :=
  if i + 4 <= x.size
  then ByteArray.to_be32 x (i + 4) (out.push (UInt32.of_be32 x[i]! x[i+1]! x[i+2]! x[i+3]!))
  else out

partial def ByteArray.to_le32 (x: ByteArray) (i: Nat := 0) (out: Array UInt32 := #[]): Array UInt32 :=
  if i + 4 <= x.size
  then ByteArray.to_le32 x (i + 4) (out.push (UInt32.of_be32 x[i+3]! x[i+2]! x[i+1]! x[i]!))
  else out

partial def ByteArray.of_le32 (x: Subarray UInt32) (i: Nat := 0) (out: ByteArray := ByteArray.mkEmpty (x.size * 4)): ByteArray
  := if h: i < x.size
      then ByteArray.of_le32 x (i + 1) (out ++ UInt32.to_le x[i])
      else out

#eval (ByteArray.of_le32 #[0xff000001, 0xcc000002].toSubarray).data == #[1, 0, 0, 0xff, 2, 0, 0, 0xcc]
#eval ByteArray.to_le32 (ByteArray.of_le32 #[0xff000001, 0xcc000002].toSubarray) == #[0xff000001, 0xcc000002]

partial def ByteArray.of_be32 (x: Subarray UInt32) (i: Nat := 0) (out: ByteArray := ByteArray.mkEmpty (x.size * 4)): ByteArray
  := if h: i < x.size
      then ByteArray.of_be32 x (i + 1) (out ++ UInt32.to_be x[i])
      else out

end ByteArray
