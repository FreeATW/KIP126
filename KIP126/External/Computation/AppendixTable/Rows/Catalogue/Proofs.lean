import KIP126.External.Computation.AppendixTable.Rows.Catalogue.Data
import KIP126.External.Computation.AppendixTable.Rows.Predicates
import KIP126.External.Computation.AppendixTable.Proofs

/-!
# Checks of the transcribed Appendix catalogue

These proofs check row counts, unique keys, metadata, and display bands.
They do not prove the spectral-sequence facts recorded by the source tables.
-/

namespace KIP126.Computation

theorem appendixRowsChunk1_valid : appendixRowsChunk1.all AppendixRow.validBool = true := by decide

theorem appendixRowsChunk2_valid : appendixRowsChunk2.all AppendixRow.validBool = true := by decide

theorem appendixRowsChunk3_valid : appendixRowsChunk3.all AppendixRow.validBool = true := by decide

theorem appendixRowsChunk4_valid : appendixRowsChunk4.all AppendixRow.validBool = true := by decide

theorem appendixRowsChunk5_valid : appendixRowsChunk5.all AppendixRow.validBool = true := by decide

theorem appendixRowsChunk6_valid : appendixRowsChunk6.all AppendixRow.validBool = true := by decide

theorem appendixRowsChunk7_valid : appendixRowsChunk7.all AppendixRow.validBool = true := by decide

theorem appendixRowsChunk8_valid : appendixRowsChunk8.all AppendixRow.validBool = true := by decide

theorem appendixRowsChunk9_valid : appendixRowsChunk9.all AppendixRow.validBool = true := by decide

theorem appendixRowsChunk10_valid : appendixRowsChunk10.all AppendixRow.validBool = true := by decide

theorem appendixRowsChunk11_valid : appendixRowsChunk11.all AppendixRow.validBool = true := by decide

theorem appendixRows_valid : appendixRowsValid = true := by
  simp [appendixRowsValid, appendixRows, List.all_append,
    appendixRowsChunk1_valid, appendixRowsChunk2_valid, appendixRowsChunk3_valid,
    appendixRowsChunk4_valid, appendixRowsChunk5_valid, appendixRowsChunk6_valid,
    appendixRowsChunk7_valid, appendixRowsChunk8_valid, appendixRowsChunk9_valid,
    appendixRowsChunk10_valid, appendixRowsChunk11_valid]

theorem appendixRowsChunk1_length : appendixRowsChunk1.length = 40 := by decide

theorem appendixRowsChunk1_keys_nodup : appendixRowsChunk1Keys.Nodup := by decide

theorem appendixRowsChunk1_keys_lower : ∀ x ∈ appendixRowsChunk1Keys, 1 ≤ x := by decide

theorem appendixRowsChunk1_keys_upper : ∀ x ∈ appendixRowsChunk1Keys, x ≤ 40 := by decide

theorem appendixRowsChunk2_length : appendixRowsChunk2.length = 40 := by decide

theorem appendixRowsChunk2_keys_nodup : appendixRowsChunk2Keys.Nodup := by decide

theorem appendixRowsChunk2_keys_lower : ∀ x ∈ appendixRowsChunk2Keys, 41 ≤ x := by decide

theorem appendixRowsChunk2_keys_upper : ∀ x ∈ appendixRowsChunk2Keys, x ≤ 80 := by decide

theorem appendixRowsChunk3_length : appendixRowsChunk3.length = 40 := by decide

theorem appendixRowsChunk3_keys_nodup : appendixRowsChunk3Keys.Nodup := by decide

theorem appendixRowsChunk3_keys_lower : ∀ x ∈ appendixRowsChunk3Keys, 81 ≤ x := by decide

theorem appendixRowsChunk3_keys_upper : ∀ x ∈ appendixRowsChunk3Keys, x ≤ 120 := by decide

theorem appendixRowsChunk4_length : appendixRowsChunk4.length = 40 := by decide

theorem appendixRowsChunk4_keys_nodup : appendixRowsChunk4Keys.Nodup := by decide

theorem appendixRowsChunk4_keys_lower : ∀ x ∈ appendixRowsChunk4Keys, 121 ≤ x := by decide

theorem appendixRowsChunk4_keys_upper : ∀ x ∈ appendixRowsChunk4Keys, x ≤ 160 := by decide

theorem appendixRowsChunk5_length : appendixRowsChunk5.length = 40 := by decide

theorem appendixRowsChunk5_keys_nodup : appendixRowsChunk5Keys.Nodup := by decide

theorem appendixRowsChunk5_keys_lower : ∀ x ∈ appendixRowsChunk5Keys, 161 ≤ x := by decide

theorem appendixRowsChunk5_keys_upper : ∀ x ∈ appendixRowsChunk5Keys, x ≤ 200 := by decide

theorem appendixRowsChunk6_length : appendixRowsChunk6.length = 40 := by decide

theorem appendixRowsChunk6_keys_nodup : appendixRowsChunk6Keys.Nodup := by decide

theorem appendixRowsChunk6_keys_lower : ∀ x ∈ appendixRowsChunk6Keys, 201 ≤ x := by decide

theorem appendixRowsChunk6_keys_upper : ∀ x ∈ appendixRowsChunk6Keys, x ≤ 240 := by decide

theorem appendixRowsChunk7_length : appendixRowsChunk7.length = 40 := by decide

theorem appendixRowsChunk7_keys_nodup : appendixRowsChunk7Keys.Nodup := by decide

theorem appendixRowsChunk7_keys_lower : ∀ x ∈ appendixRowsChunk7Keys, 241 ≤ x := by decide

theorem appendixRowsChunk7_keys_upper : ∀ x ∈ appendixRowsChunk7Keys, x ≤ 280 := by decide

theorem appendixRowsChunk8_length : appendixRowsChunk8.length = 40 := by decide

theorem appendixRowsChunk8_keys_nodup : appendixRowsChunk8Keys.Nodup := by decide

theorem appendixRowsChunk8_keys_lower : ∀ x ∈ appendixRowsChunk8Keys, 281 ≤ x := by decide

theorem appendixRowsChunk8_keys_upper : ∀ x ∈ appendixRowsChunk8Keys, x ≤ 320 := by decide

theorem appendixRowsChunk9_length : appendixRowsChunk9.length = 40 := by decide

theorem appendixRowsChunk9_keys_nodup : appendixRowsChunk9Keys.Nodup := by decide

theorem appendixRowsChunk9_keys_lower : ∀ x ∈ appendixRowsChunk9Keys, 321 ≤ x := by decide

theorem appendixRowsChunk9_keys_upper : ∀ x ∈ appendixRowsChunk9Keys, x ≤ 360 := by decide

theorem appendixRowsChunk10_length : appendixRowsChunk10.length = 40 := by decide

theorem appendixRowsChunk10_keys_nodup : appendixRowsChunk10Keys.Nodup := by decide

theorem appendixRowsChunk10_keys_lower : ∀ x ∈ appendixRowsChunk10Keys, 361 ≤ x := by decide

theorem appendixRowsChunk10_keys_upper : ∀ x ∈ appendixRowsChunk10Keys, x ≤ 400 := by decide

theorem appendixRowsChunk11_length : appendixRowsChunk11.length = 1 := by decide

theorem appendixRowsChunk11_keys_nodup : appendixRowsChunk11Keys.Nodup := by decide

theorem appendixRowsChunk11_keys_lower : ∀ x ∈ appendixRowsChunk11Keys, 401 ≤ x := by decide

theorem appendixRowsChunk11_keys_upper : ∀ x ∈ appendixRowsChunk11Keys, x ≤ 401 := by decide

lemma upper_append {l₁ l₂ : List Nat} {hi₁ hi₂ : Nat}
    (h₁ : ∀ x ∈ l₁, x ≤ hi₁) (h₂ : ∀ x ∈ l₂, x ≤ hi₂) :
    ∀ x ∈ l₁ ++ l₂, x ≤ max hi₁ hi₂ := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact le_trans (h₁ x hx) (Nat.le_max_left _ _)
  · exact le_trans (h₂ x hx) (Nat.le_max_right _ _)

lemma append_nodup_of_bounds {l₁ l₂ : List Nat} {hi lo : Nat}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup)
    (upper : ∀ x ∈ l₁, x ≤ hi) (lower : ∀ x ∈ l₂, lo ≤ x)
    (bound : hi < lo) : (l₁ ++ l₂).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨h₁, h₂, ?_⟩
  intro a ha b hb hab
  have ha' := upper a ha
  have hb' := lower b hb
  omega

theorem appendixRowsKeysPrefix1_nodup : appendixRowsKeysPrefix1.Nodup := by simpa [appendixRowsKeysPrefix1] using appendixRowsChunk1_keys_nodup

theorem appendixRowsKeysPrefix1_upper : ∀ x ∈ appendixRowsKeysPrefix1, x ≤ 40 := by simpa [appendixRowsKeysPrefix1] using appendixRowsChunk1_keys_upper

theorem appendixRowsKeysPrefix2_nodup : appendixRowsKeysPrefix2.Nodup := by
  apply append_nodup_of_bounds appendixRowsKeysPrefix1_nodup appendixRowsChunk2_keys_nodup appendixRowsKeysPrefix1_upper appendixRowsChunk2_keys_lower (by decide)

theorem appendixRowsKeysPrefix2_upper : ∀ x ∈ appendixRowsKeysPrefix2, x ≤ 80 := by
  simpa [appendixRowsKeysPrefix2] using upper_append appendixRowsKeysPrefix1_upper appendixRowsChunk2_keys_upper

theorem appendixRowsKeysPrefix3_nodup : appendixRowsKeysPrefix3.Nodup := by
  apply append_nodup_of_bounds appendixRowsKeysPrefix2_nodup appendixRowsChunk3_keys_nodup appendixRowsKeysPrefix2_upper appendixRowsChunk3_keys_lower (by decide)

theorem appendixRowsKeysPrefix3_upper : ∀ x ∈ appendixRowsKeysPrefix3, x ≤ 120 := by
  simpa [appendixRowsKeysPrefix3] using upper_append appendixRowsKeysPrefix2_upper appendixRowsChunk3_keys_upper

theorem appendixRowsKeysPrefix4_nodup : appendixRowsKeysPrefix4.Nodup := by
  apply append_nodup_of_bounds appendixRowsKeysPrefix3_nodup appendixRowsChunk4_keys_nodup appendixRowsKeysPrefix3_upper appendixRowsChunk4_keys_lower (by decide)

theorem appendixRowsKeysPrefix4_upper : ∀ x ∈ appendixRowsKeysPrefix4, x ≤ 160 := by
  simpa [appendixRowsKeysPrefix4] using upper_append appendixRowsKeysPrefix3_upper appendixRowsChunk4_keys_upper

theorem appendixRowsKeysPrefix5_nodup : appendixRowsKeysPrefix5.Nodup := by
  apply append_nodup_of_bounds appendixRowsKeysPrefix4_nodup appendixRowsChunk5_keys_nodup appendixRowsKeysPrefix4_upper appendixRowsChunk5_keys_lower (by decide)

theorem appendixRowsKeysPrefix5_upper : ∀ x ∈ appendixRowsKeysPrefix5, x ≤ 200 := by
  simpa [appendixRowsKeysPrefix5] using upper_append appendixRowsKeysPrefix4_upper appendixRowsChunk5_keys_upper

theorem appendixRowsKeysPrefix6_nodup : appendixRowsKeysPrefix6.Nodup := by
  apply append_nodup_of_bounds appendixRowsKeysPrefix5_nodup appendixRowsChunk6_keys_nodup appendixRowsKeysPrefix5_upper appendixRowsChunk6_keys_lower (by decide)

theorem appendixRowsKeysPrefix6_upper : ∀ x ∈ appendixRowsKeysPrefix6, x ≤ 240 := by
  simpa [appendixRowsKeysPrefix6] using upper_append appendixRowsKeysPrefix5_upper appendixRowsChunk6_keys_upper

theorem appendixRowsKeysPrefix7_nodup : appendixRowsKeysPrefix7.Nodup := by
  apply append_nodup_of_bounds appendixRowsKeysPrefix6_nodup appendixRowsChunk7_keys_nodup appendixRowsKeysPrefix6_upper appendixRowsChunk7_keys_lower (by decide)

theorem appendixRowsKeysPrefix7_upper : ∀ x ∈ appendixRowsKeysPrefix7, x ≤ 280 := by
  simpa [appendixRowsKeysPrefix7] using upper_append appendixRowsKeysPrefix6_upper appendixRowsChunk7_keys_upper

theorem appendixRowsKeysPrefix8_nodup : appendixRowsKeysPrefix8.Nodup := by
  apply append_nodup_of_bounds appendixRowsKeysPrefix7_nodup appendixRowsChunk8_keys_nodup appendixRowsKeysPrefix7_upper appendixRowsChunk8_keys_lower (by decide)

theorem appendixRowsKeysPrefix8_upper : ∀ x ∈ appendixRowsKeysPrefix8, x ≤ 320 := by
  simpa [appendixRowsKeysPrefix8] using upper_append appendixRowsKeysPrefix7_upper appendixRowsChunk8_keys_upper

theorem appendixRowsKeysPrefix9_nodup : appendixRowsKeysPrefix9.Nodup := by
  apply append_nodup_of_bounds appendixRowsKeysPrefix8_nodup appendixRowsChunk9_keys_nodup appendixRowsKeysPrefix8_upper appendixRowsChunk9_keys_lower (by decide)

theorem appendixRowsKeysPrefix9_upper : ∀ x ∈ appendixRowsKeysPrefix9, x ≤ 360 := by
  simpa [appendixRowsKeysPrefix9] using upper_append appendixRowsKeysPrefix8_upper appendixRowsChunk9_keys_upper

theorem appendixRowsKeysPrefix10_nodup : appendixRowsKeysPrefix10.Nodup := by
  apply append_nodup_of_bounds appendixRowsKeysPrefix9_nodup appendixRowsChunk10_keys_nodup appendixRowsKeysPrefix9_upper appendixRowsChunk10_keys_lower (by decide)

theorem appendixRowsKeysPrefix10_upper : ∀ x ∈ appendixRowsKeysPrefix10, x ≤ 400 := by
  simpa [appendixRowsKeysPrefix10] using upper_append appendixRowsKeysPrefix9_upper appendixRowsChunk10_keys_upper

theorem appendixRowsKeysPrefix11_nodup : appendixRowsKeysPrefix11.Nodup := by
  apply append_nodup_of_bounds appendixRowsKeysPrefix10_nodup appendixRowsChunk11_keys_nodup appendixRowsKeysPrefix10_upper appendixRowsChunk11_keys_lower (by decide)

theorem appendixRowsKeysPrefix11_upper : ∀ x ∈ appendixRowsKeysPrefix11, x ≤ 401 := by
  simpa [appendixRowsKeysPrefix11] using upper_append appendixRowsKeysPrefix10_upper appendixRowsChunk11_keys_upper

theorem appendixRows_length : appendixRows.length = 401 := by
  simp [appendixRows, appendixRowsChunk1_length, appendixRowsChunk2_length,
    appendixRowsChunk3_length, appendixRowsChunk4_length, appendixRowsChunk5_length,
    appendixRowsChunk6_length, appendixRowsChunk7_length, appendixRowsChunk8_length,
    appendixRowsChunk9_length, appendixRowsChunk10_length, appendixRowsChunk11_length]

theorem appendixRows_keys_nodup : (appendixRows.map AppendixRow.key).Nodup := by
  simpa [appendixRows, appendixRowsKeysPrefix1, appendixRowsKeysPrefix2,
    appendixRowsKeysPrefix3, appendixRowsKeysPrefix4, appendixRowsKeysPrefix5,
    appendixRowsKeysPrefix6, appendixRowsKeysPrefix7, appendixRowsKeysPrefix8,
    appendixRowsKeysPrefix9, appendixRowsKeysPrefix10, appendixRowsKeysPrefix11,
    appendixRowsChunk1Keys, appendixRowsChunk2Keys, appendixRowsChunk3Keys,
    appendixRowsChunk4Keys, appendixRowsChunk5Keys, appendixRowsChunk6Keys,
    appendixRowsChunk7Keys, appendixRowsChunk8Keys, appendixRowsChunk9Keys,
    appendixRowsChunk10Keys, appendixRowsChunk11Keys] using
      appendixRowsKeysPrefix11_nodup

theorem appendixZeroBands_valid : appendixZeroBandsValid = true := by decide

theorem appendixZeroBands_length : appendixZeroBands.length = 9 := by decide

end KIP126.Computation
