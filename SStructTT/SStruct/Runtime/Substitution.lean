import SStructTT.SStruct.Runtime.Resolution

namespace SStruct.Erasure
namespace Runtime
variable {Srt : Type} [ord : SrtOrder Srt]

@[aesop safe (rule_sets := [subst]) [constructors]]
inductive AgreeSubst :
  (Var -> Erasure.Tm Srt) ->
  (Var -> Erasure.Tm Srt) ->
  Nat -> Dynamic.Ctx Srt -> Heap Srt -> Prop
where
  | nil {H σ σ'} :
    WR H ->
    HLower H ord.e ->
    AgreeSubst σ σ' 0 [] H
  | cons {Δ H σ σ' A x r s} :
    AgreeSubst σ σ' x Δ H ->
    AgreeSubst (up σ) (up σ') (x + 1) (A :⟨r, s⟩ Δ) H
  | wk_im {Δ H σ σ' A m m' s} :
    AgreeSubst σ σ' 0 Δ H ->
    AgreeSubst (m .: σ) (m' .: σ') 0 (A :⟨.im, s⟩ Δ) H
  | wk_ex {Δ H1 H2 H3 σ σ' m m' A s} :
    WR H2 ->
    HLower H2 s ->
    HMerge H1 H2 H3 ->
    H2 ;; m ▷ m' ->
    AgreeSubst σ σ' 0 Δ H1 ->
    AgreeSubst (m .: σ) (m' .: σ') 0 (A :⟨.ex, s⟩ Δ) H3
