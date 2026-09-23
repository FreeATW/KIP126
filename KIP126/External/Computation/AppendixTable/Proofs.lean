import KIP126.External.Computation.AppendixTable.Data

/-! Enumeration and locator properties of the twelve source tables. -/

namespace KIP126.Computation.AppendixTableId

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

end KIP126.Computation.AppendixTableId
