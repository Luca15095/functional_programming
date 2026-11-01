import RegexDeriv.Parse

/-!
# Beispiele

`#eval`-Beispiele aus dem Paper.

`#eval` zeigt ein Ergebnis nur an. `#guard` prüft, dass ein Ausdruck `true` ist,
und lässt sonst `lake build` fehlschlagen.
-/

open Regex

namespace Examples

-- Abkürzungen für die Buchstaben in den Beispielen
def a : Regex := char 'a'
def b : Regex := char 'b'
def x : Regex := char 'x'

/-! ## Ableitungen -/

-- x* abgeleitet nach 'x' ergibt ε · x*
#eval deriv 'x' (star x)
#guard deriv 'x' (star x) = seq eps (star x)

-- x* abgeleitet nach 'y' ergibt ∅ · x* (beschreibt die leere Sprache)
#guard deriv 'y' (star x) = seq phi (star x)

/-! ## Matcher -/

-- x* passt auf "", "x" und "xxx", aber nicht auf "xy"
#guard matchDeriv [] (star x)
#guard matchDeriv "x".toList (star x)
#guard matchDeriv "xxx".toList (star x)
#guard !matchDeriv "xy".toList (star x)

-- (a + ab)(b + ε) aus dem Paper
def r1 : Regex := seq (choice a (seq a b)) (choice b eps)

#guard matchDeriv "a".toList r1
#guard matchDeriv "ab".toList r1
#guard matchDeriv "abb".toList r1
#guard !matchDeriv "b".toList r1

-- (a + (b + ab))* aus dem Paper
def r2 : Regex := star (choice a (choice b (seq a b)))

#guard matchDeriv "ab".toList r2
#guard matchDeriv "abba".toList r2
#guard !matchDeriv "abc".toList r2

end Examples
