import SStructTT.SStruct.Erasure.Progress
import SStructTT.SStruct.Runtime.Preservation
open ARS

namespace SStruct.Erasure
namespace Runtime
variable {Srt : Type} [ord : SrtOrder Srt]

@[simp]def measure : Tm Srt -> Nat
  | .var _ => 0
  | .lam _ _ => 1
  | .app m n => measure m + measure n
  | .tup m n _ => measure m + measure n + 1
  | .prj m _ => measure m
  | .tt => 1
  | .ff => 1
  | .ite m _ _ => measure m
  | .drop _ m => measure m + 1
  | .ptr _ => 0
  | .null => 0

def Measure : State Srt -> State Srt -> Prop  :=
  InvImage (. < .) (fun m => measure m.2)

lemma measure_decrease {H1 H2 : Heap Srt} {m1 m2} :
    (Union Step0 Step1) (H1, m1) (H2, m2) -> measure m2 < measure m1 := by
  intro st; induction m1 generalizing H1 H2 m2
  all_goals simp_all
  case var =>
    cases st with
    | inl st => cases st
    | inr st => cases st
  case lam =>
    cases st with
    | inl st => cases st
    | inr st => cases st; simp
  case app ihm ihn =>
    cases st with
    | inl st =>
      cases st
      case app_M st => simp[ihm (Or.inl st)]
      case app_N st => simp[ihn (Or.inl st)]
    | inr st =>
      cases st
      case app_M st => simp[ihm (Or.inr st)]
      case app_N st => simp[ihn (Or.inr st)]
  case tup ihm ihn =>
    cases st with
    | inl st =>
      cases st
      case tup_M st => simp[ihm (Or.inl st)]
      case tup_N st => simp[ihn (Or.inl st)]
    | inr st =>
      cases st
      case tup_M st => simp[ihm (Or.inr st)]
      case tup_N st => simp[ihn (Or.inr st)]
      case alloc_box => simp
      case alloc_tup => simp
  case prj ihm ihn =>
    cases st with
    | inl st =>
      cases st
      case prj_M st => simp[ihm (Or.inl st)]
    | inr st =>
      cases st
      case prj_M st => simp[ihm (Or.inr st)]
  case tt =>
    cases st with
    | inl st => cases st
    | inr st => cases st; simp
  case ff =>
    cases st with
    | inl st => cases st
    | inr st => cases st; simp
  case ite ihm ihn1 ihn2 =>
    cases st with
    | inl st =>
      cases st
      case ite_M st => simp[ihm (Or.inl st)]
    | inr st =>
      cases st
      case ite_M st => simp[ihm (Or.inr st)]
  case drop ihm ihn =>
    cases st with
    | inl st => cases st; simp
    | inr st => cases st
  case ptr =>
    cases st with
    | inl st => cases st
    | inr st => cases st
  case null =>
    cases st with
    | inl st => cases st
    | inr st => cases st

lemma measure_subrelation :
    Subrelation (flip (@Union (State Srt) Step0 Step1)) Measure := by
  intro ⟨H1, m1⟩ ⟨H2, m2⟩ st
  apply measure_decrease st

lemma wf_initial_steps : WellFounded (flip (@Union (State Srt) Step0 Step1)) := by
  apply Subrelation.wf (@measure_subrelation Srt ord)
  apply InvImage.wf
  apply Nat.lt_wfRel.wf

lemma sn_initial_steps {m : State Srt} : SN (Union Step0 Step1) m := by
  have ⟨acc⟩ := @wf_initial_steps Srt ord
  apply SN.ofAcc
  apply acc
