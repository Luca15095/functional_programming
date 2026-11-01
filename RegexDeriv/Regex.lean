/-!
# Reguläre Ausdrücke und Ableitungen

Regex-AST, `nullable`, `deriv` (Ableitung `r\l`) und `matchDeriv`.
Übersetzt aus der Haskell-Referenz (Abschnitt *Derivative-based matcher*).
-/

/-- Reguläre Ausdrücke. Entspricht `data R` im Haskell-Code:
`Phi`, `Eps`, `L Char`, `Seq R R`, `Choice R R`, `Star R`. -/
inductive Regex where
  | phi                          -- leere Sprache ∅
  | eps                          -- leeres Wort ε
  | char (c : Char)              -- einzelner Buchstabe
  | seq (r s : Regex)            -- Verkettung r · s
  | choice (r s : Regex)         -- Auswahl r + s
  | star (r : Regex)             -- Kleene-Stern r*
  deriving Repr, DecidableEq

namespace Regex

/-- `nullable r = true` genau dann, wenn das leere Wort in `L(r)` liegt. -/
def nullable : Regex → Bool
  | phi        => false
  | eps        => true
  | char _     => false
  | choice r s => nullable r || nullable s
  | seq r s    => nullable r && nullable s
  | star _     => true

/-- Ableitung `r\c`: beschreibt alle Wörter `w`, für die `c :: w` in `L(r)` liegt.
Wie im Haskell-Code kommt der Buchstabe zuerst. -/
def deriv (c : Char) : Regex → Regex
  | phi        => phi
  | eps        => phi
  | char d     => if c = d then eps else phi
  | choice r s => choice (deriv c r) (deriv c s)
  | seq r s    =>
      if nullable r then choice (seq (deriv c r) s) (deriv c s)
      else seq (deriv c r) s
  | star r     => seq (deriv c r) (star r)

/-- Matcher: leitet nacheinander nach jedem Buchstaben ab und prüft am Ende `nullable`.
Im Haskell-Code passiert das in der Hilfsfunktion `go`; hier rekursiert
`matchDeriv` direkt über das Wort. -/
def matchDeriv : List Char → Regex → Bool
  | [],      r => nullable r
  | c :: cs, r => matchDeriv cs (deriv c r)

end Regex
