import RegexDeriv.Regex

/-!
# Parse-Bäume

Parse-Bäume `Val` (im Paper und im Haskell-Code `U`), `flatten` (im Paper `|v|`)
und `Valid v r` (im Paper `⊢ v : r`, Fig. 1).
-/

/-- Parse-Bäume. Ein Parse-Baum zeigt, *wie* ein Wort zu einem regulären Ausdruck passt.

Entspricht `data U` im Haskell-Code. Den Haskell-Konstruktor `Nil` (Baum für `Phi`)
gibt es hier nicht: `phi` passt auf kein Wort, also gibt es dafür auch keinen
Parse-Baum (so auch in Fig. 1 des Papers). -/
inductive Val where
  | empty                        -- Baum für ε                 (Haskell: Empty,  Paper: ())
  | letter (c : Char)            -- Baum für einen Buchstaben  (Haskell: Letter)
  | left (v : Val)               -- linke Seite einer Auswahl  (Haskell: LeftU)
  | right (v : Val)              -- rechte Seite einer Auswahl (Haskell: RightU)
  | pair (v1 v2 : Val)           -- Baum für eine Verkettung   (Haskell: Pair)
  | list (vs : List Val)         -- Baum für einen Stern, ein Teilbaum pro Wiederholung
                                 --                            (Haskell: List)
  deriving Repr, BEq

namespace Val

mutual
  /-- `flatten v` (im Paper `|v|`): das Wort, das im Baum steht, also alle
  Buchstaben an den Blättern von links nach rechts. -/
  def flatten : Val → List Char
    | empty      => []
    | letter c   => [c]
    | left v     => flatten v
    | right v    => flatten v
    | pair v1 v2 => flatten v1 ++ flatten v2
    | list vs    => flattenList vs

  /-- Hilfsfunktion für den Stern: hängt die Wörter aller Teilbäume aneinander. -/
  def flattenList : List Val → List Char
    | []      => []
    | v :: vs => flatten v ++ flattenList vs
end

end Val

/-- `Valid v r` (im Paper `⊢ v : r`, Fig. 1): `v` ist ein gültiger Parse-Baum für `r`.

Ein Baum ist gültig, wenn seine Form zur Form des Ausdrucks passt. Für `phi` gibt
es keinen Konstruktor: kein Baum ist für `phi` gültig. -/
inductive Valid : Val → Regex → Prop where
  /-- `⊢ () : ε` -/
  | eps : Valid .empty .eps
  /-- `⊢ c : c` -/
  | char (c : Char) : Valid (.letter c) (.char c)
  /-- Ist `v` gültig für `r`, dann ist `Left v` gültig für `r + s`. -/
  | left {v : Val} {r s : Regex} :
      Valid v r → Valid (.left v) (.choice r s)
  /-- Ist `v` gültig für `s`, dann ist `Right v` gültig für `r + s`. -/
  | right {v : Val} {r s : Regex} :
      Valid v s → Valid (.right v) (.choice r s)
  /-- Sind `v₁` gültig für `r` und `v₂` gültig für `s`, dann ist `(v₁, v₂)` gültig für `r · s`. -/
  | seq {v₁ v₂ : Val} {r s : Regex} :
      Valid v₁ r → Valid v₂ s → Valid (.pair v₁ v₂) (.seq r s)
  /-- `⊢ [] : r*` (null Wiederholungen) -/
  | starNil {r : Regex} : Valid (.list []) (.star r)
  /-- Ist `v` gültig für `r` und `vs` gültig für `r*`, dann ist `v :: vs` gültig für `r*`
  (eine Wiederholung mehr). -/
  | starCons {v : Val} {vs : List Val} {r : Regex} :
      Valid v r → Valid (.list vs) (.star r) → Valid (.list (v :: vs)) (.star r)
