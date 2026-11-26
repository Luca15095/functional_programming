# POSIX-Regex-Parsing mit Ableitungen in Lean 4

Arbeit an der Hochschule Karlsruhe, Luca Vossler, betreut von Prof. Dr. Martin Sulzmann.

## Aufgabe

Der Parser für reguläre Ausdrücke aus *POSIX Regular Expression Parsing with Derivatives*
(Sulzmann, Lu, FLOPS 2014) wird in Lean 4 implementiert und seine Korrektheit bewiesen.
Grundlage ist die [Haskell-Referenz](https://sulzmann.github.io/ProgrammingParadigms/pp-regular-expressions.html)
(Abschnitte *Semantics*, *Derivative-based matcher*, *POSIX parser*; im Paper Fig. 1 und Fig. 3).

Bewiesen ist: Liefert `parse` einen Parse-Baum `v`, dann ist `v` ein gültiger Baum für `r`
(`⊢ v : r`), `v` steht genau für das Eingabewort (`|v| = w`), und `|v| ∈ L(r)`.

```lean
theorem parse_sound (r : Regex) (w : List Char) (v : Val) (h : parse r w = some v) :
    Valid v r ∧ flatten v = w ∧ InLang (flatten v) r
```

Der Beweis kommt ohne `sorry`, eigene Axiome oder `native_decide` aus
(`#print axioms Regex.parse_sound` zeigt nur die Standardaxiome `propext` und `Quot.sound`).

## Aufbau

| Datei | Inhalt |
|---|---|
| `RegexDeriv/Regex.lean` | `Regex`, `nullable`, `deriv`, `matchDeriv` |
| `RegexDeriv/ParseTree.lean` | Parse-Bäume `Val`, `flatten` (`\|v\|`), `Valid` (`⊢ v : r`) |
| `RegexDeriv/Language.lean` | Sprache `InLang w r` (`w ∈ L(r)`) als induktive Aussage |
| `RegexDeriv/Parse.lean` | `mkEps`, `inj`, `parse` |
| `RegexDeriv/Examples.lean` | Beispiele aus dem Paper |
| `RegexDeriv/Testing.lean` | Property-based Tests mit Plausible |
| `RegexDeriv/Proofs.lean` | `mkEps`-Lemma, `inj`-Lemma, Hauptsatz `parse_sound` |

## Bauen

Voraussetzung ist [elan](https://github.com/leanprover/elan) (Lean-Version in `lean-toolchain`).

```bash
lake build
```

Der Build prüft alles auf einmal: die Beispiele (`#guard`), die Plausible-Tests
(1000 Zufallsfälle pro Eigenschaft, fester Startwert) und alle Beweise.

## Interessante Aspekte von Lean

- **Totalität.** Jede Funktion muss für alle Eingaben ein Ergebnis liefern und terminieren.
  Statt `error` geben `mkEps`, `inj` und `parse` deshalb `Option Val` zurück.
  Die Terminierung erkennt Lean selbst, weil alle Funktionen strukturell rekursiv sind.
- **Programm und Beweis in einer Sprache.** `L(r)` und `⊢ v : r` sind induktive Aussagen
  (`InLang`, `Valid`), deren Regeln eins zu eins den Definitionen entsprechen. Bewiesen wird
  über genau das `parse`, das auch mit `#eval` läuft.
- **Der Beweis folgt der Rekursion.** `mkEps` und `inj` rekursieren über `r`, `parse` über das
  Wort. Die Beweise sind Induktionen über dieselben Strukturen, mit einem Fall pro Gleichung.
- **Tests beim Kompilieren.** `#guard` und Plausible laufen bei jedem Build. Plausible hat
  absichtlich eingebaute Fehler in `inj` mit kleinen Gegenbeispielen gefunden, bevor die
  Beweise begonnen wurden.
- **Verschachtelte Typen.** `Val` enthält `List Val`. `flatten` wird deshalb zusammen mit einer
  Hilfsfunktion für Listen gegenseitig rekursiv definiert (`mutual`), und Gleichheit muss über
  `BEq` statt `DecidableEq` abgeleitet werden.

## Vergleich mit Haskell

Die Übersetzung ist größtenteils 1:1: dieselben Datentypen, dieselben Gleichungen, nur andere Syntax.

```haskell
deriv x (Star r) = Seq (deriv x r) (Star r)

inj (Star r) (Seq rd _) l (Pair (u, List us)) =
    List $ (inj r rd l u) : us
```

```lean
| star r => seq (deriv c r) (star r)

| star r, c, pair v1 (list vs) => (inj r c v1).map (fun v1' => list (v1' :: vs))
```

Unterschiede:

| Haskell | Lean | Grund |
|---|---|---|
| `error "..."` | `none` (`Option`) | Funktionen müssen total sein |
| `mkEps Phi = Nil` | `none`, kein `Nil` | für `φ` gibt es keinen gültigen Baum |
| `inj r (r\l) l u` | `inj r c v` | der Fall von `deriv` ist an der Form von `v` ablesbar; so rekursiert `inj` strukturell über `r` |
| `let Pair (u', u'') = u` | Muster `left (pair v1 v2)` | kein Laufzeitfehler bei falscher Form, stattdessen `none` |
| lokale Funktion `go` in `matchDeriv` | direkte Rekursion über das Wort | einfacher für Beweise |



## `inj`: Haskell vs. Lean

### Unterschied

```haskell
-- Haskell
inj :: R -> R -> Char -> U -> U          -- r, r\l, Buchstabe, Baum
```
```lean
-- Lean
def inj : Regex → Char → Val → Option Val  -- r, Buchstabe, Baum
```

- **Rückgabe:** Haskell `U`, Lean `Option Val` (`some v` oder `none`)
- **Fehlerfälle:** Haskell bricht mit `error` ab, Lean liefert `none`
- **Argument `r\l`:** Haskell bekommt es übergeben, Lean nicht

### Wieso ist die Anpassung in Lean notwendig?

**`Option` statt `error`: notwendig**
- Lean akzeptiert nur Funktionen, die für jede Eingabe ein Ergebnis liefern
- Grund: Funktionen werden auch in Beweisen benutzt, ein Absturz würde die Logik kaputt machen
- Haskell-`inj` kann zur Laufzeit abstürzen:
  - letzte Zeile ruft `error` auf
  - `let Pair (u', u'') = u` scheitert, wenn `u` kein `Pair` ist
- In Lean werden diese Fälle zu `none`

**Kein `r\l`: nicht notwendig, aber einfacher**
- `r\l` ist immer `deriv l r`, also überflüssig
- Welcher Fall von `deriv` vorlag, sieht man an der Form des Baums `v`
- Beispiel `seq r s`:
  - `r` nicht nullable → Ableitung ist `seq` → `v` ist `pair`
  - `r` nullable → Ableitung ist `choice` → `v` ist `left` oder `right`
- Dadurch: `inj` läuft nur rekursiv über `r` → Beweis ist eine einfache Induktion über `r`
- Mit `r\l` wäre es auch gegangen, aber der Beweis wäre aufwendiger

### Könnte man das gleiche auch in Haskell machen?

- **Ja, beides**
- Haskell hat `Maybe` (= Leans `Option`), statt `error` also `Nothing`
- Man kann genauso auf die Form des Baums matchen statt auf `r\l`
- Beispiel, gleicher Fall in beiden Sprachen:
  ```haskell
  inj (Seq r1 _) l (Pair (u1, u2)) = (\u1' -> Pair (u1', u2)) <$> inj r1 l u1
  ```
  ```lean
  | seq r _, c, pair v1 v2 => (inj r c v1).map (fun v1' => pair v1' v2)
  ```
- **Einziger Unterschied:** Haskell *erlaubt* Abstürze (höchstens eine Warnung), Lean *verbietet* sie
