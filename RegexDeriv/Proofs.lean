import RegexDeriv.Parse
import RegexDeriv.Language

/-!
# Korrektheitsbeweise

Lemmata zu `mkEps` und `inj` und der Hauptsatz `parse_sound`.
-/

namespace Regex

open Val

/-! ## Gültige Bäume und `mkEps` -/

/-- Ein gültiger Baum ergibt ein Wort der Sprache. -/
theorem valid_inLang {v : Val} {r : Regex} (h : Valid v r) : InLang (flatten v) r := by
  induction h with
  | eps => exact InLang.eps
  | char c => exact InLang.char c
  | left _ ih => exact InLang.choiceLeft ih
  | right _ ih => exact InLang.choiceRight ih
  | seq _ _ ih₁ ih₂ => exact InLang.seq ih₁ ih₂
  | starNil => exact InLang.starNil
  | starCons _ _ ih₁ ih₂ => exact InLang.starCons ih₁ ih₂

/-- `mkEps`-Lemma: Der Baum von `mkEps` ist gültig und steht für das leere Wort. -/
theorem mkEps_sound (r : Regex) (v : Val) (h : mkEps r = some v) :
    Valid v r ∧ flatten v = [] := by
  induction r generalizing v with
  | phi => simp [mkEps] at h
  | eps =>
    simp [mkEps] at h
    subst h
    exact ⟨Valid.eps, rfl⟩
  | char c => simp [mkEps] at h
  | choice r s ihr ihs =>
    simp only [mkEps] at h
    by_cases hr : nullable r = true
    · simp [hr] at h
      obtain ⟨v1, h1, rfl⟩ := h
      have ⟨hv1, hf1⟩ := ihr v1 h1
      exact ⟨Valid.left hv1, hf1⟩
    · simp [hr] at h
      by_cases hs : nullable s = true
      · simp [hs] at h
        obtain ⟨v2, h2, rfl⟩ := h
        have ⟨hv2, hf2⟩ := ihs v2 h2
        exact ⟨Valid.right hv2, hf2⟩
      · simp [hs] at h
  | seq r s ihr ihs =>
    simp only [mkEps] at h
    cases h1 : mkEps r with
    | none =>
      simp [h1] at h
    | some v1 =>
      cases h2 : mkEps s with
      | none =>
        simp [h1, h2] at h
      | some v2 =>
        simp [h1, h2] at h
        subst h
        have ⟨hv1, hf1⟩ := ihr v1 h1
        have ⟨hv2, hf2⟩ := ihs v2 h2
        refine ⟨Valid.seq hv1 hv2, ?_⟩
        show flatten v1 ++ flatten v2 = []
        rw [hf1, hf2]
        rfl
  | star r =>
    simp [mkEps] at h
    subst h
    exact ⟨Valid.starNil, rfl⟩

theorem mkEps_inLang (r : Regex) (v : Val) (h : mkEps r = some v) :
    InLang (flatten v) r ∧ flatten v = [] := by
  have ⟨hv, hf⟩ := mkEps_sound r v h
  exact ⟨valid_inLang hv, hf⟩

end Regex
