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

/-! ## Das `inj`-Lemma -/

theorem valid_star_list {v : Val} {r : Regex} (h : Valid v (.star r)) : ∃ vs, v = list vs := by
  cases h with
  | starNil => exact ⟨[], rfl⟩
  | starCons _ _ => exact ⟨_, rfl⟩

/-- `inj`-Lemma: Aus einem gültigen Baum für `deriv c r` macht `inj` einen gültigen
Baum für `r`, der `c` vorne dazubekommt.

Induktion über `r`. In jedem Fall wird `deriv c r` ausgerechnet und mit `cases hv`
bestimmt, welche Form `v` haben kann. -/
theorem inj_sound (r : Regex) (c : Char) (v v' : Val)
    (hv : Valid v (deriv c r)) (h : inj r c v = some v') :
    Valid v' r ∧ flatten v' = c :: flatten v := by
  induction r generalizing v v' with
  | phi =>
    simp only [deriv] at hv
    cases hv
  | eps =>
    simp only [deriv] at hv
    cases hv
  | char d =>
    simp only [deriv] at hv
    by_cases hcd : c = d
    · subst hcd
      simp at hv
      cases hv
      simp [inj] at h
      subst h
      exact ⟨Valid.char c, rfl⟩
    · simp [hcd] at hv
      cases hv
  | choice r s ihr ihs =>
    simp only [deriv] at hv
    cases hv with
    | @left v1 _ _ hv1 =>
      simp [inj] at h
      obtain ⟨v1', h1, rfl⟩ := h
      have ⟨hv1', hf1⟩ := ihr v1 v1' hv1 h1
      exact ⟨Valid.left hv1', hf1⟩
    | @right v2 _ _ hv2 =>
      simp [inj] at h
      obtain ⟨v2', h2, rfl⟩ := h
      have ⟨hv2', hf2⟩ := ihs v2 v2' hv2 h2
      exact ⟨Valid.right hv2', hf2⟩
  | seq r s ihr ihs =>
    simp only [deriv] at hv
    by_cases hr : nullable r = true
    · simp [hr] at hv
      cases hv with
      | @left v0 _ _ hv0 =>
        -- v = left (pair v1 v2): der Buchstabe gehört zu r
        cases hv0 with
        | @seq v1 v2 _ _ hv1 hv2 =>
          simp [inj] at h
          obtain ⟨v1', h1, rfl⟩ := h
          have ⟨hv1', hf1⟩ := ihr v1 v1' hv1 h1
          refine ⟨Valid.seq hv1' hv2, ?_⟩
          show flatten v1' ++ flatten v2 = c :: (flatten v1 ++ flatten v2)
          rw [hf1, List.cons_append]
      | @right v2 _ _ hv2 =>
        -- v = right v2: r bekommt das leere Wort (mkEps-Lemma), der Buchstabe gehört zu s
        simp only [inj] at h
        cases hm : mkEps r with
        | none =>
          simp [hm] at h
        | some v1 =>
          cases hi : inj s c v2 with
          | none =>
            simp [hm, hi] at h
          | some v2' =>
            simp [hm, hi] at h
            subst h
            have ⟨hv1, hf1⟩ := mkEps_sound r v1 hm
            have ⟨hv2', hf2⟩ := ihs v2 v2' hv2 hi
            refine ⟨Valid.seq hv1 hv2', ?_⟩
            show flatten v1 ++ flatten v2' = c :: flatten v2
            rw [hf1, hf2, List.nil_append]
    · -- r nicht nullable: v = pair v1 v2, der Buchstabe gehört zu r
      simp [hr] at hv
      cases hv with
      | @seq v1 v2 _ _ hv1 hv2 =>
        simp [inj] at h
        obtain ⟨v1', h1, rfl⟩ := h
        have ⟨hv1', hf1⟩ := ihr v1 v1' hv1 h1
        refine ⟨Valid.seq hv1' hv2, ?_⟩
        show flatten v1' ++ flatten v2 = c :: (flatten v1 ++ flatten v2)
        rw [hf1, List.cons_append]
  | star r ih =>
    simp only [deriv] at hv
    cases hv with
    | @seq v1 v2 _ _ hv1 hv2 =>
      obtain ⟨vs, rfl⟩ := valid_star_list hv2
      simp [inj] at h
      obtain ⟨v1', h1, rfl⟩ := h
      have ⟨hv1', hf1⟩ := ih v1 v1' hv1 h1
      refine ⟨Valid.starCons hv1' hv2, ?_⟩
      show flatten v1' ++ flatten (list vs) = c :: (flatten v1 ++ flatten (list vs))
      rw [hf1, List.cons_append]

/-! ## Der Hauptsatz -/

/-- Induktion über das Wort: Basisfall mit dem `mkEps`-Lemma, Schritt mit dem `inj`-Lemma. -/
theorem parse_valid (r : Regex) (w : List Char) (v : Val) (h : parse r w = some v) :
    Valid v r ∧ flatten v = w := by
  induction w generalizing r v with
  | nil =>
    simp only [parse] at h
    by_cases hn : nullable r = true
    · simp [hn] at h
      exact mkEps_sound r v h
    · simp [hn] at h
  | cons c cs ih =>
    simp only [parse] at h
    cases hp : parse (deriv c r) cs with
    | none =>
      simp [hp] at h
    | some u =>
      simp [hp] at h
      have ⟨hu, hfu⟩ := ih (deriv c r) u hp
      have ⟨hv, hfv⟩ := inj_sound r c u v hu h
      refine ⟨hv, ?_⟩
      rw [hfv, hfu]

/-- Hauptsatz: Kernziel `|v| ∈ L(r)` und die Zusatzziele `⊢ v : r` und `|v| = w`. -/
theorem parse_sound (r : Regex) (w : List Char) (v : Val) (h : parse r w = some v) :
    Valid v r ∧ flatten v = w ∧ InLang (flatten v) r := by
  have ⟨hv, hf⟩ := parse_valid r w v h
  exact ⟨hv, hf, valid_inLang hv⟩

/-- Das Kernziel in der Formulierung der Aufgabe. -/
theorem parse_inLang (r : Regex) (w : List Char) (v : Val) :
    parse r w = some v → InLang (flatten v) r := by
  intro h
  exact (parse_sound r w v h).2.2

theorem parse_word_inLang (r : Regex) (w : List Char) (v : Val) (h : parse r w = some v) :
    InLang w r := by
  have ⟨_, hf, hl⟩ := parse_sound r w v h
  rw [hf] at hl
  exact hl

end Regex
