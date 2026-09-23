import KIP126.External.Computation.AppendixTable.Rows.Catalogue.Rows001To160
import KIP126.External.Computation.AppendixTable.Rows.Catalogue.Rows161To320
import KIP126.External.Computation.AppendixTable.Rows.Catalogue.Rows321To401

/-!
# Transcribed Appendix catalogue

The 401 row records and nine empty display bands retain their paper locators.
These are source data. Their recorded differential or permanence status is
not a Lean theorem about the Adams spectral sequence; using that status as a
mathematical fact still requires explicit external evidence.
-/

namespace KIP126.Computation

/-- All 401 nonempty rows transcribed from `aimpaper/main.tex`. -/
def appendixRows : List AppendixRow := appendixRowsChunk1 ++ appendixRowsChunk2 ++ appendixRowsChunk3 ++ appendixRowsChunk4 ++ appendixRowsChunk5 ++ appendixRowsChunk6 ++ appendixRowsChunk7 ++ appendixRowsChunk8 ++ appendixRowsChunk9 ++ appendixRowsChunk10 ++ appendixRowsChunk11

/-- The nine explicitly empty filtration bands printed in the appendix. -/
def appendixZeroBands : List AppendixZeroBand := [
  { table := .s122, low := 9, high := 10, locator := { line := 2842 } },
  { table := .s122, low := 0, high := 7, locator := { line := 2844 } },
  { table := .s123, low := 25, high := 25, locator := { line := 2855 } },
  { table := .s123, low := 21, high := 22, locator := { line := 2860 } },
  { table := .s123, low := 0, high := 7, locator := { line := 2899 } },
  { table := .s124Low, low := 0, high := 5, locator := { line := 2988 } },
  { table := .s125Low, low := 0, high := 4, locator := { line := 3074 } },
  { table := .s126Low, low := 0, high := 1, locator := { line := 3167 } },
  { table := .s127Low, low := 0, high := 0, locator := { line := 3286 } },
]

def appendixRowsValid : Bool := appendixRows.all AppendixRow.validBool

def appendixRowsChunk1Keys : List Nat := appendixRowsChunk1.map AppendixRow.key

def appendixRowsChunk2Keys : List Nat := appendixRowsChunk2.map AppendixRow.key

def appendixRowsChunk3Keys : List Nat := appendixRowsChunk3.map AppendixRow.key

def appendixRowsChunk4Keys : List Nat := appendixRowsChunk4.map AppendixRow.key

def appendixRowsChunk5Keys : List Nat := appendixRowsChunk5.map AppendixRow.key

def appendixRowsChunk6Keys : List Nat := appendixRowsChunk6.map AppendixRow.key

def appendixRowsChunk7Keys : List Nat := appendixRowsChunk7.map AppendixRow.key

def appendixRowsChunk8Keys : List Nat := appendixRowsChunk8.map AppendixRow.key

def appendixRowsChunk9Keys : List Nat := appendixRowsChunk9.map AppendixRow.key

def appendixRowsChunk10Keys : List Nat := appendixRowsChunk10.map AppendixRow.key

def appendixRowsChunk11Keys : List Nat := appendixRowsChunk11.map AppendixRow.key

def appendixRowsKeysPrefix1 : List Nat := appendixRowsChunk1Keys

def appendixRowsKeysPrefix2 : List Nat := appendixRowsKeysPrefix1 ++ appendixRowsChunk2Keys

def appendixRowsKeysPrefix3 : List Nat := appendixRowsKeysPrefix2 ++ appendixRowsChunk3Keys

def appendixRowsKeysPrefix4 : List Nat := appendixRowsKeysPrefix3 ++ appendixRowsChunk4Keys

def appendixRowsKeysPrefix5 : List Nat := appendixRowsKeysPrefix4 ++ appendixRowsChunk5Keys

def appendixRowsKeysPrefix6 : List Nat := appendixRowsKeysPrefix5 ++ appendixRowsChunk6Keys

def appendixRowsKeysPrefix7 : List Nat := appendixRowsKeysPrefix6 ++ appendixRowsChunk7Keys

def appendixRowsKeysPrefix8 : List Nat := appendixRowsKeysPrefix7 ++ appendixRowsChunk8Keys

def appendixRowsKeysPrefix9 : List Nat := appendixRowsKeysPrefix8 ++ appendixRowsChunk9Keys

def appendixRowsKeysPrefix10 : List Nat := appendixRowsKeysPrefix9 ++ appendixRowsChunk10Keys

def appendixRowsKeysPrefix11 : List Nat := appendixRowsKeysPrefix10 ++ appendixRowsChunk11Keys

def appendixZeroBandsValid : Bool := appendixZeroBands.all AppendixZeroBand.validBool

end KIP126.Computation
