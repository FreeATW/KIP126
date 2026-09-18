import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fintype.Card

/-!
# The twelve tables in the Kervaire computation catalogue

The first table is the Hopf-cofiber table immediately before the Appendix.
The remaining eleven tables are the sphere tables in the Appendix.  These
identifiers locate a table; they make no assertion about any row's truth.
The PDF page numbers refer to `aimpaper/2412.10879.pdf`, and the source line
numbers refer to `aimpaper/main.tex` in this repository.
-/

namespace KIP126.Computation

/-- The spectrum named by a table. -/
inductive AppendixSpectrum
  | sphere
  | hopfCofiber
  deriving DecidableEq, Repr, Inhabited

/-- Stable identities for all twelve paper tables. -/
inductive AppendixTableId
  | cnu126
  | s122
  | s123
  | s124High
  | s124Low
  | s125High
  | s125Low
  | s126High
  | s126Low
  | s127High
  | s127Middle
  | s127Low
  deriving DecidableEq, Repr, Inhabited

namespace AppendixTableId

/-- The numbering printed in the paper PDF. -/
def paperNumber : AppendixTableId → ℕ
  | .cnu126 => 1
  | .s122 => 2
  | .s123 => 3
  | .s124High => 4
  | .s124Low => 5
  | .s125High => 6
  | .s125Low => 7
  | .s126High => 8
  | .s126Low => 9
  | .s127High => 10
  | .s127Middle => 11
  | .s127Low => 12

/-- Exact TeX label used for cross-references in `aimpaper/main.tex`. -/
def texLabel : AppendixTableId → String
  | .cnu126 => "Table:Cnu126"
  | .s122 => "Table:S122"
  | .s123 => "Table:S123"
  | .s124High => "Table:S124.13"
  | .s124Low => "Table:S124.12"
  | .s125High => "Table:S125.20"
  | .s125Low => "Table:S125.19"
  | .s126High => "Table:S126.11"
  | .s126Low => "Table:S126.10"
  | .s127High => "Table:S127.21"
  | .s127Middle => "Table:S127.20"
  | .s127Low => "Table:S127.9"

/-- Printed PDF page containing the table caption. -/
def pdfPage : AppendixTableId → ℕ
  | .cnu126 => 54
  | .s122 => 56
  | .s123 => 57
  | .s124High => 58
  | .s124Low => 59
  | .s125High => 59
  | .s125Low => 60
  | .s126High => 61
  | .s126Low => 62
  | .s127High => 62
  | .s127Middle => 63
  | .s127Low => 64

/-- Line containing the `\begin{table}` command. -/
def sourceStart : AppendixTableId → ℕ
  | .cnu126 => 2738
  | .s122 => 2804
  | .s123 => 2851
  | .s124High => 2908
  | .s124Low => 2962
  | .s125High => 2994
  | .s125Low => 3020
  | .s126High => 3081
  | .s126Low => 3138
  | .s127High => 3173
  | .s127Middle => 3200
  | .s127Low => 3258

/-- Line containing the table's TeX label. -/
def sourceEnd : AppendixTableId → ℕ
  | .cnu126 => 2772
  | .s122 => 2847
  | .s123 => 2902
  | .s124High => 2957
  | .s124Low => 2991
  | .s125High => 3017
  | .s125Low => 3077
  | .s126High => 3134
  | .s126Low => 3170
  | .s127High => 3196
  | .s127Middle => 3255
  | .s127Low => 3289

def spectrum : AppendixTableId → AppendixSpectrum
  | .cnu126 => .hopfCofiber
  | _ => .sphere

def stem : AppendixTableId → ℕ
  | .cnu126 | .s126High | .s126Low => 126
  | .s122 => 122
  | .s123 => 123
  | .s124High | .s124Low => 124
  | .s125High | .s125Low => 125
  | .s127High | .s127Middle | .s127Low => 127

/-- The inclusive Adams-filtration band printed in the caption. -/
def filtrationRange : AppendixTableId → ℕ × ℕ
  | .cnu126 => (9, 14)
  | .s122 | .s123 => (0, 25)
  | .s124High => (13, 25)
  | .s124Low => (0, 12)
  | .s125High => (20, 25)
  | .s125Low => (0, 19)
  | .s126High => (11, 25)
  | .s126Low => (0, 10)
  | .s127High => (21, 25)
  | .s127Middle => (10, 20)
  | .s127Low => (0, 9)

/-- The canonical table order, matching the PDF numbering. -/
def all : List AppendixTableId :=
  [.cnu126, .s122, .s123, .s124High, .s124Low, .s125High,
   .s125Low, .s126High, .s126Low, .s127High, .s127Middle, .s127Low]

instance : Fintype AppendixTableId where
  elems := {.cnu126, .s122, .s123, .s124High, .s124Low, .s125High,
    .s125Low, .s126High, .s126Low, .s127High, .s127Middle, .s127Low}
  complete id := by cases id <;> simp

theorem all_complete (id : AppendixTableId) : id ∈ all := by
  cases id <;> decide

theorem all_nodup : all.Nodup := by decide

theorem all_length : all.length = 12 := by decide

theorem card : Fintype.card AppendixTableId = 12 := by decide

theorem paperNumbers_nodup : (all.map paperNumber).Nodup := by decide

theorem texLabels_nodup : (all.map texLabel).Nodup := by decide

theorem sourceRange_valid (id : AppendixTableId) :
    id.sourceStart ≤ id.sourceEnd := by
  cases id <;> decide

theorem filtrationRange_valid (id : AppendixTableId) :
    id.filtrationRange.1 ≤ id.filtrationRange.2 := by
  cases id <;> decide

end AppendixTableId

end KIP126.Computation
