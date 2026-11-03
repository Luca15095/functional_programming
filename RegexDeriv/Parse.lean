import RegexDeriv.ParseTree

/-!
# POSIX-Parser

`mkEps`, `inj` und `parse` (Fig. 3) aus der Haskell-Referenz (Abschnitt *POSIX parser*).
Wo der Haskell-Code `error` aufruft, liefern die Funktionen hier `none`.
-/

namespace Regex

open Val

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

/-- Anders als im Haskell-Code bekommt `inj` nicht die Ableitung `r\c` als Argument.
Welcher Fall von `deriv` vorlag, zeigt die Form von `v`. So ist `inj` strukturell
rekursiv über `r`. -/
def inj : Regex → Char → Val → Option Val
  | char d,     c, empty    => if c = d then some (letter c) else none
  | choice r _, c, left v   => (inj r c v).map left
  | choice _ s, c, right v  => (inj s c v).map right
  -- r nicht nullable: deriv c (seq r s) = seq (deriv c r) s
  | seq r _,    c, pair v1 v2         => (inj r c v1).map (fun v1' => pair v1' v2)
  -- r nullable: deriv c (seq r s) = choice (seq (deriv c r) s) (deriv c s)
  | seq r _,    c, left (pair v1 v2)  => (inj r c v1).map (fun v1' => pair v1' v2)
  | seq r s,    c, right v2           =>
      match mkEps r, inj s c v2 with
      | some v1, some v2' => some (pair v1 v2')
      | _, _              => none
  | star r,     c, pair v1 (list vs)  => (inj r c v1).map (fun v1' => list (v1' :: vs))
  | _,          _, _        => none

def parse : Regex → List Char → Option Val
  | r, []      => if nullable r then mkEps r else none
  | r, c :: cs =>
      match parse (deriv c r) cs with
      | some v => inj r c v
      | none   => none

end Regex
