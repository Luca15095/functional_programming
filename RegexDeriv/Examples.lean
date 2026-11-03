import RegexDeriv.Parse
import RegexDeriv.Language

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

/-! ## Parse-Bäume und `flatten`

Zu einem Wort kann es mehrere Parse-Bäume geben. `flatten` liefert für alle
dasselbe Wort; der Parser soll später den POSIX-Baum auswählen. -/

open Val

-- r1 = (a + ab)(b + ε) mit dem Wort "ab": zwei verschiedene Bäume

-- POSIX-Baum aus dem Paper: (Right (a, b), Right ())
def v1 : Val := pair (right (pair (letter 'a') (letter 'b'))) (right empty)
-- anderer Baum: (Left a, Left b)
def v1' : Val := pair (left (letter 'a')) (left (letter 'b'))

#eval flatten v1
#guard flatten v1 = "ab".toList
#guard flatten v1' = "ab".toList
#guard v1 != v1'

-- r2 = (a + (b + ab))* mit dem Wort "ab": eine oder zwei Wiederholungen

-- POSIX-Baum aus dem Paper: [Right (Right (a, b))]
def v2 : Val := list [right (right (pair (letter 'a') (letter 'b')))]
-- anderer Baum: [Left a, Right (Left b)]
def v2' : Val := list [left (letter 'a'), right (left (letter 'b'))]

#guard flatten v2 = "ab".toList
#guard flatten v2' = "ab".toList

-- null Wiederholungen ergeben das leere Wort
#guard flatten (list []) = []

/-! ## Parser

`parse` muss aus allen möglichen Bäumen den POSIX-Baum auswählen. -/

-- Die beiden Beispiele aus dem Paper
#eval parse r1 "ab".toList
#guard parse r1 "ab".toList == some v1
#guard parse r2 "ab".toList == some v2

-- weitere Wörter für r1 = (a + ab)(b + ε)
#guard parse r1 "a".toList   == some (pair (left (letter 'a')) (right empty))
#guard parse r1 "abb".toList ==
  some (pair (right (pair (letter 'a') (letter 'b'))) (left (letter 'b')))
#guard parse r1 "b".toList   == none

-- r2 = (a + (b + ab))* mit "abba": erst "ab", dann "b", dann "a"
#guard parse r2 "abba".toList ==
  some (list [right (right (pair (letter 'a') (letter 'b'))),
              right (left (letter 'b')),
              left (letter 'a')])

-- x* mit "" und "xx"
#guard parse (star x) [] == some (list [])
#guard parse (star x) "xx".toList == some (list [letter 'x', letter 'x'])

-- mkEps wählt bei einer Auswahl die linke Seite, wenn sie nullable ist
#guard mkEps (choice (star a) eps) == some (left (list []))
#guard mkEps (choice a eps)        == some (right empty)

/-! ## Sprache `InLang` und gültige Bäume `Valid`

`InLang` und `Valid` sind Aussagen (`Prop`), keine Funktionen. Man kann sie nicht
mit `#eval` ausrechnen, sondern muss sie beweisen. `example` ist ein Satz ohne
Namen: Wenn die Datei baut, hat Lean den Beweis akzeptiert. -/

-- "ab" ∈ L(r1), mit Taktiken bewiesen: "ab" = "a" ++ "b",
-- "a" kommt aus der linken Seite von (a + ab), "b" aus der linken Seite von (b + ε)
example : InLang ['a', 'b'] r1 := by
  apply InLang.seq (w₁ := ['a']) (w₂ := ['b'])
  · apply InLang.choiceLeft
    exact InLang.char 'a'
  · apply InLang.choiceLeft
    exact InLang.char 'b'

-- "xx" ∈ L(x*): zwei Wiederholungen, dann Schluss
example : InLang ['x', 'x'] (star x) := by
  apply InLang.starCons (w₁ := ['x']) (w₂ := ['x'])
  · exact InLang.char 'x'
  · apply InLang.starCons (w₁ := ['x']) (w₂ := [])
    · exact InLang.char 'x'
    · exact InLang.starNil

-- Kein Wort liegt in L(φ): es gibt keine Regel, die auf φ endet
example (w : List Char) : ¬ InLang w phi := by
  intro h
  cases h

-- Beide Bäume für "ab" aus dem Abschnitt oben sind gültig für r1,
-- direkt als Term aufgeschrieben: die Konstruktoren bilden den Baum nach
example : Valid v1 r1 :=
  Valid.seq (Valid.right (Valid.seq (Valid.char 'a') (Valid.char 'b'))) (Valid.right Valid.eps)

example : Valid v1' r1 :=
  Valid.seq (Valid.left (Valid.char 'a')) (Valid.left (Valid.char 'b'))

example : Valid v2 r2 :=
  Valid.starCons (Valid.right (Valid.right (Valid.seq (Valid.char 'a') (Valid.char 'b'))))
    Valid.starNil

-- Ein Baum für den falschen Buchstaben ist nicht gültig
example : ¬ Valid (letter 'a') b := by
  intro h
  cases h

end Examples
