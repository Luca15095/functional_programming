import RegexDeriv.Regex

/-!
# Sprache eines regulären Ausdrucks

`InLang w r` heißt `w ∈ L(r)` (Haskell-Referenz, Abschnitt *Semantics*).
Für `phi` gibt es keine Regel. Der Stern ist rekursiv beschrieben:
leeres Wort, oder ein Wort aus `L(r)` gefolgt von einem Wort aus `L(r*)`.
-/

inductive InLang : List Char → Regex → Prop where
  | eps : InLang [] .eps
  | char (c : Char) : InLang [c] (.char c)
  | choiceLeft {w : List Char} {r s : Regex} :
      InLang w r → InLang w (.choice r s)
  | choiceRight {w : List Char} {r s : Regex} :
      InLang w s → InLang w (.choice r s)
  | seq {w₁ w₂ : List Char} {r s : Regex} :
      InLang w₁ r → InLang w₂ s → InLang (w₁ ++ w₂) (.seq r s)
  | starNil {r : Regex} : InLang [] (.star r)
  | starCons {w₁ w₂ : List Char} {r : Regex} :
      InLang w₁ r → InLang w₂ (.star r) → InLang (w₁ ++ w₂) (.star r)
