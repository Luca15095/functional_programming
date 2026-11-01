import RegexDeriv.Regex

/-!
# Parse-Bäume

Parse-Bäume `Val` (im Paper und im Haskell-Code `U`) und `flatten` (im Paper `|v|`).
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
