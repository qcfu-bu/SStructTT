# SStructTT


| logic    | contraction | weakening |
| -------- | ----------- | --------- |
| linear   | no          | no        |
| affine   | no          | yes       |
| relevant | yes         | no        |
| unbound  | yes         | yes       |

If there are `Γ ⊢ m : A`, `A` is unbound and `B` is affine, can we weaken `Γ` with `B`?
```
Γ ⊢ m : A
-----------------
Γ, x : B ⊢ m : A


(λ(x : A). ⟨x, x⟩) m ~> ⟨m, m⟩
```