/-!
# Reguläre Ausdrücke und Ableitungen

`Regex`, `nullable`, `deriv` und `matchDeriv` aus der Haskell-Referenz
(Abschnitt *Derivative-based matcher*).
-/

inductive Regex where
  | phi
  | eps
  | char (c : Char)
  | seq (r s : Regex)
  | choice (r s : Regex)
  | star (r : Regex)
  deriving Repr, DecidableEq

namespace Regex

def nullable : Regex → Bool
  | phi        => false
  | eps        => true
  | char _     => false
  | choice r s => nullable r || nullable s
  | seq r s    => nullable r && nullable s
  | star _     => true

/-- Ableitung `r\c`. -/
def deriv (c : Char) : Regex → Regex
  | phi        => phi
  | eps        => phi
  | char d     => if c = d then eps else phi
  | choice r s => choice (deriv c r) (deriv c s)
  | seq r s    =>
      if nullable r then choice (seq (deriv c r) s) (deriv c s)
      else seq (deriv c r) s
  | star r     => seq (deriv c r) (star r)

def matchDeriv : List Char → Regex → Bool
  | [],      r => nullable r
  | c :: cs, r => matchDeriv cs (deriv c r)

end Regex
