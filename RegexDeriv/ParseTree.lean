import RegexDeriv.Regex

/-!
# Parse-Bäume

`Val` (Haskell: `U`), `flatten` (Paper: `|v|`) und `Valid v r` (Paper: `⊢ v : r`, Fig. 1).
-/

/-- Parse-Bäume, entspricht `U` im Haskell-Code (`Empty`, `Letter`, `LeftU`,
`RightU`, `Pair`, `List`). `Nil` fehlt: Für `phi` gibt es keinen Parse-Baum. -/
inductive Val where
  | empty
  | letter (c : Char)
  | left (v : Val)
  | right (v : Val)
  | pair (v1 v2 : Val)
  | list (vs : List Val)
  deriving Repr, BEq

namespace Val

mutual
  def flatten : Val → List Char
    | empty      => []
    | letter c   => [c]
    | left v     => flatten v
    | right v    => flatten v
    | pair v1 v2 => flatten v1 ++ flatten v2
    | list vs    => flattenList vs

  def flattenList : List Val → List Char
    | []      => []
    | v :: vs => flatten v ++ flattenList vs
end

end Val

/-- `Valid v r`: `v` ist ein gültiger Parse-Baum für `r` (`⊢ v : r`, Fig. 1). -/
inductive Valid : Val → Regex → Prop where
  | eps : Valid .empty .eps
  | char (c : Char) : Valid (.letter c) (.char c)
  | left {v : Val} {r s : Regex} :
      Valid v r → Valid (.left v) (.choice r s)
  | right {v : Val} {r s : Regex} :
      Valid v s → Valid (.right v) (.choice r s)
  | seq {v₁ v₂ : Val} {r s : Regex} :
      Valid v₁ r → Valid v₂ s → Valid (.pair v₁ v₂) (.seq r s)
  | starNil {r : Regex} : Valid (.list []) (.star r)
  | starCons {v : Val} {vs : List Val} {r : Regex} :
      Valid v r → Valid (.list vs) (.star r) → Valid (.list (v :: vs)) (.star r)
