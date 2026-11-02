import RegexDeriv.ParseTree

/-!
# POSIX-Parser

`mkEps`, `inj` und `parse` (Fig. 3 im Paper), übersetzt aus der Haskell-Referenz
(Abschnitt *POSIX parser*).

Wo der Haskell-Code `error "..."` aufruft, liefern die Lean-Funktionen `none`.
Deshalb geben alle drei Funktionen `Option Val` zurück: `some v` heißt
„Baum `v` gefunden“, `none` heißt „kein Baum“.
-/

namespace Regex

open Val

/-- `mkEps r`: der POSIX-Baum für das leere Wort, falls `r` nullable ist.
Bei einer Auswahl wird die linke Seite bevorzugt, wenn sie nullable ist. -/
def mkEps : Regex → Option Val
  | phi        => none
  | eps        => some empty
  | char _     => none
  | choice r s =>
      if nullable r then (mkEps r).map left
      else if nullable s then (mkEps s).map right
      else none
  | seq r s    =>
      match mkEps r, mkEps s with
      | some v1, some v2 => some (pair v1 v2)
      | _, _             => none
  | star _     => some (list [])

/-- `inj r c v`: Wenn `v` ein Baum für die Ableitung `deriv c r` ist, setzt `inj`
den Buchstaben `c` wieder ein und liefert einen Baum für `r`.

Im Haskell-Code bekommt `inj` zusätzlich die Ableitung `r\c` als Argument und
unterscheidet die Fälle nach deren Form. Hier reicht die Form von `r` und `v`:
die Form von `v` zeigt schon, welcher Fall von `deriv` vorlag. -/
def inj : Regex → Char → Val → Option Val
  -- deriv c (char d) = eps, wenn c = d. Der Baum für eps ist empty.
  | char d,     c, empty    => if c = d then some (letter c) else none
  -- deriv c (choice r s) = choice (deriv c r) (deriv c s)
  | choice r _, c, left v   => (inj r c v).map left
  | choice _ s, c, right v  => (inj s c v).map right
  -- r nicht nullable: deriv c (seq r s) = seq (deriv c r) s
  | seq r _,    c, pair v1 v2         => (inj r c v1).map (fun v1' => pair v1' v2)
  -- r nullable: deriv c (seq r s) = choice (seq (deriv c r) s) (deriv c s)
  -- links: der Buchstabe gehört zu r
  | seq r _,    c, left (pair v1 v2)  => (inj r c v1).map (fun v1' => pair v1' v2)
  -- rechts: r bekommt das leere Wort, der Buchstabe gehört zu s
  | seq r s,    c, right v2           =>
      match mkEps r, inj s c v2 with
      | some v1, some v2' => some (pair v1 v2')
      | _, _              => none
  -- deriv c (star r) = seq (deriv c r) (star r): eine weitere Wiederholung vorne
  | star r,     c, pair v1 (list vs)  => (inj r c v1).map (fun v1' => list (v1' :: vs))
  -- alle anderen Kombinationen passen nicht zusammen (im Haskell-Code: error)
  | _,          _, _        => none

/-- `parse r w`: der POSIX-Parse-Baum für das Wort `w`, oder `none`, wenn `w`
nicht zu `r` passt.

Wie `matchDeriv` wird nach jedem Buchstaben abgeleitet. Am Ende baut `mkEps`
den Baum für das leere Wort, und auf dem Rückweg setzt `inj` die Buchstaben
wieder ein. -/
def parse : Regex → List Char → Option Val
  | r, []      => if nullable r then mkEps r else none
  | r, c :: cs =>
      match parse (deriv c r) cs with
      | some v => inj r c v
      | none   => none

end Regex
