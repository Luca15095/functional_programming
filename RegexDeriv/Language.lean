import RegexDeriv.Regex

/-!
# Sprache eines regulären Ausdrucks

`InLang w r` als induktive Proposition: das Wort `w` liegt in `L(r)`.
Übersetzt aus der Haskell-Referenz (Abschnitt *Background → Semantics*):

* `L(ε) = { ε }`
* `L(x) = { x }`
* `L(φ) = { }`
* `L(r + s) = { w | w ∈ L(r) oder w ∈ L(s) }`
* `L(r · s) = { v · w | v ∈ L(r) und w ∈ L(s) }`
* `L(r*) = { ε } ∪ { w₁ · … · wₙ | w₁, …, wₙ ∈ L(r), n ≥ 1 }`

Jede Regel wird ein Konstruktor. Für `φ` gibt es keinen Konstruktor, weil
`L(φ)` leer ist. Den Stern beschreiben wir rekursiv: entweder das leere Wort,
oder ein Wort aus `L(r)` gefolgt von einem Wort aus `L(r*)`.
-/

/-- `InLang w r`: Das Wort `w` liegt in der Sprache `L(r)`. -/
inductive InLang : List Char → Regex → Prop where
  /-- `ε ∈ L(ε)` -/
  | eps : InLang [] .eps
  /-- `c ∈ L(c)` -/
  | char (c : Char) : InLang [c] (.char c)
  /-- Ist `w ∈ L(r)`, dann ist `w ∈ L(r + s)`. -/
  | choiceLeft {w : List Char} {r s : Regex} :
      InLang w r → InLang w (.choice r s)
  /-- Ist `w ∈ L(s)`, dann ist `w ∈ L(r + s)`. -/
  | choiceRight {w : List Char} {r s : Regex} :
      InLang w s → InLang w (.choice r s)
  /-- Ist `w₁ ∈ L(r)` und `w₂ ∈ L(s)`, dann ist `w₁ ++ w₂ ∈ L(r · s)`. -/
  | seq {w₁ w₂ : List Char} {r s : Regex} :
      InLang w₁ r → InLang w₂ s → InLang (w₁ ++ w₂) (.seq r s)
  /-- `ε ∈ L(r*)` (null Wiederholungen) -/
  | starNil {r : Regex} : InLang [] (.star r)
  /-- Ist `w₁ ∈ L(r)` und `w₂ ∈ L(r*)`, dann ist `w₁ ++ w₂ ∈ L(r*)`
  (eine Wiederholung mehr). -/
  | starCons {w₁ w₂ : List Char} {r : Regex} :
      InLang w₁ r → InLang w₂ (.star r) → InLang (w₁ ++ w₂) (.star r)
