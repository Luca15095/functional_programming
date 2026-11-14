import Plausible
import RegexDeriv.Parse
import RegexDeriv.Language

/-!
# Property-based Tests

Die Beweisziele werden vorab mit Plausible getestet. Ein Gegenbeispiel lässt
`lake build` fehlschlagen. `inLangB` und `validB` sind ausführbare Gegenstücke
zu `InLang` und `Valid` und nur für die Tests gedacht.
-/

namespace Testing

open Plausible Regex Val

/-! ## Zufallsgeneratoren -/

/-- Nur `a` und `b`, damit zufällige Wörter oft zu zufälligen Ausdrücken passen. -/
def genChar : Gen Char := Gen.elements ['a', 'b'] (by decide)

local instance (priority := high) : Arbitrary Char := ⟨genChar⟩

def genRegex : Nat → Gen Regex
  | 0     => Gen.oneOf #[pure phi, pure eps, char <$> genChar]
  | n + 1 => Gen.frequency (genRegex 0) [
      (2, genRegex 0),
      (2, choice <$> genRegex n <*> genRegex n),
      (2, seq <$> genRegex n <*> genRegex n),
      (1, star <$> genRegex n)]

instance : Arbitrary Regex := ⟨Gen.sized fun size => genRegex (min size 4)⟩

def shrinkRegex : Regex → List Regex
  | phi        => []
  | eps        => [phi]
  | char _     => [eps]
  | choice r s => [r, s] ++ (shrinkRegex r).map (choice · s) ++ (shrinkRegex s).map (choice r ·)
  | seq r s    => [r, s] ++ (shrinkRegex r).map (seq · s) ++ (shrinkRegex s).map (seq r ·)
  | star r     => [r, eps] ++ (shrinkRegex r).map star

instance : Shrinkable Regex := ⟨shrinkRegex⟩

/-! ## Ausführbare Gegenstücke zu `InLang` und `Valid` -/

def splits (w : List Char) : List (List Char × List Char) :=
  (List.range (w.length + 1)).map fun i => (w.take i, w.drop i)

/-- `w` lässt sich in höchstens `n` nicht-leere Stücke zerlegen, die alle `p` erfüllen. -/
def starB (p : List Char → Bool) : Nat → List Char → Bool
  | _,     []      => true
  | 0,     _ :: _  => false
  | n + 1, w       => (splits w).any fun (w₁, w₂) => !w₁.isEmpty && p w₁ && starB p n w₂

def inLangB : List Char → Regex → Bool
  | _, phi        => false
  | w, eps        => w.isEmpty
  | w, char c     => w == [c]
  | w, choice r s => inLangB w r || inLangB w s
  | w, seq r s    => (splits w).any fun (w₁, w₂) => inLangB w₁ r && inLangB w₂ s
  | w, star r     => starB (fun w₁ => inLangB w₁ r) w.length w

def validB : Val → Regex → Bool
  | .empty,      eps        => true
  | .letter c,   char d     => c == d
  | .left v,     choice r _ => validB v r
  | .right v,    choice _ s => validB v s
  | .pair v₁ v₂, seq r s    => validB v₁ r && validB v₂ s
  | .list vs,    star r     => vs.all fun v => validB v r
  | _,           _          => false

/-! ## Eigenschaften -/

/-- Hauptsatz -/
def parseSound (r : Regex) (w : List Char) : Bool :=
  match parse r w with
  | some v => validB v r && flatten v == w && inLangB (flatten v) r
  | none   => true

/-- `mkEps`-Lemma -/
def mkEpsSound (r : Regex) : Bool :=
  match mkEps r with
  | some v => validB v r && (flatten v).isEmpty
  | none   => true

/-- `inj`-Lemma. Die Bäume `v` kommen aus `parse`, weil zufällige Bäume fast nie gültig sind. -/
def injSound (r : Regex) (c : Char) (w : List Char) : Bool :=
  match parse (deriv c r) w with
  | none   => true
  | some v =>
    !validB v (deriv c r) ||
      match inj r c v with
      | some v' => validB v' r && flatten v' == c :: flatten v
      | none    => false

/-- Vollständigkeit von `parse` (nur getestet) -/
def parseComplete (r : Regex) (w : List Char) : Bool :=
  (parse r w).isSome == inLangB w r

/-- Korrektheit von `matchDeriv` (nur getestet) -/
def matchCorrect (r : Regex) (w : List Char) : Bool :=
  matchDeriv w r == inLangB w r

/-! ## Tests

Fester Startwert, damit jeder Build dieselben Fälle prüft. -/

def cfg : Configuration := { numInst := 1000, maxSize := 8, randomSeed := some 2026 }

#eval Testable.check (∀ (r : Regex) (w : List Char), parseSound r w = true) cfg
#eval Testable.check (∀ (r : Regex), mkEpsSound r = true) cfg
#eval Testable.check (∀ (r : Regex) (c : Char) (w : List Char), injSound r c w = true) cfg
#eval Testable.check (∀ (r : Regex) (w : List Char), parseComplete r w = true) cfg
#eval Testable.check (∀ (r : Regex) (w : List Char), matchCorrect r w = true) cfg

end Testing
