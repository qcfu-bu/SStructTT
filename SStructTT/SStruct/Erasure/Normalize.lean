import SStructTT.SStruct.Dynamic.Normalize
import SStructTT.SStruct.Erasure.Preservation
open ARS

namespace SStruct.Erasure
variable {Srt : Type}

lemma Erased.value_step {m n : Tm Srt} :
    Value m -> m ~>> n -> False := by
  intro vl st
  cases st with
  | inl st =>
    induction st
    all_goals cases vl; try aesop
  | inr st =>
    induction st
    all_goals cases vl; try aesop

@[simp]def drop_count : Tm Srt -> Nat
  | .var _ => 0
  | .lam m _ => drop_count m
  | .app m n => drop_count m + drop_count n
  | .tup m n _ => drop_count m + drop_count n
  | .prj m n => drop_count m + drop_count n
  | .tt => 0
  | .ff => 0
  | .ite m n1 n2 => drop_count m + drop_count n1 + drop_count n2
  | .rw m => drop_count m
  | .drop m n => 1 + drop_count m + drop_count n
  | .ptr _ => 0
  | .null => 0

def DropCount : Tm Srt -> Tm Srt -> Prop  :=
  InvImage (. < .) drop_count

lemma Step0.sub_drop : Subrelation (flip Step0) (@DropCount Srt) := by
  intro m m' st; simp[DropCount,InvImage]; induction st
  all_goals try (solve| aesop)

lemma Step0.flip_wf : WellFounded (flip (@Step0 Srt)) := by
  apply Subrelation.wf Step0.sub_drop
  eta_reduce
  apply InvImage.wf
  apply Nat.lt_wfRel.wf

theorem Erased.normalize0 {m' : Tm Srt} : SN Step0 m' := by
  have ⟨h⟩ := @Step0.flip_wf Srt
  apply SN.ofAcc (h m')

variable [ord : SrtOrder Srt]

theorem Erased.normalize1 {A m : SStruct.Tm Srt} {m'} :
    [] ;; [] ⊢ m ▷ m' : A -> SN Step1 m' := by
  intro er
  have sn := er.toDynamic.normalize
  induction sn generalizing m'
  case intro m h ih =>
  constructor; intro n' st'
  have ⟨n, st, ern⟩ := er.preservation1 st'
  apply ih <;> assumption

theorem Erased.normalize {A m : SStruct.Tm Srt} {m'} :
    [] ;; [] ⊢ m ▷ m' : A -> SN Step m' := by
  intro er
  have sn := er.toDynamic.normalize
  induction sn generalizing m'
  case intro m h ih =>
  constructor; intro n' st'
  have ⟨n, st, ern⟩ := er.preservation st'
  cases st with
  | inl => aesop
  | inr =>
    subst_vars
    apply ih <;> try assumption
    sorry

-- theorem Erased.normalize {A m : SStruct.Tm Srt} {m'} :
--     [] ;; [] ⊢ m ▷ m' : A -> SN Step m' := by
--   intro er; unfold Step
--   apply Classical.byContradiction; intro nn
--   have := SN.negate nn
--   constructor

-- theorem Erased.normalize0 {m' : Tm Srt} : SN Step0 m' := by
--   induction m'
--   sorry
--   sorry
--   case app ihm ihn =>
--     replace ⟨ihm⟩ := ihm
--     replace ⟨ihn⟩ := ihn
--     constructor
--     apply Classical.byContradiction
--     intro h; simp at h
--     have ⟨x, st, nn⟩ := h
--     cases st
--     case a.h.app_M =>

--       sorry
--     case a.h.app_N =>
--       sorry


--     sorry


  -- constructor
  -- apply Classical.byContradiction; intro h
  -- simp at h
  -- induction m'
  -- case a.h.var =>
  --   have ⟨m, st, sn⟩ := h
  --   cases st
  -- case a.h.lam =>
  --   have ⟨m, st, sn⟩ := h
  --   cases st
  -- case a.h.app ihm ihn =>
  --   have ⟨m, st, sn⟩ := h
  --   cases st
  --   case app_M x st =>
  --     sorry
  --   case app_N => sorry
