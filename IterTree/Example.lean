import Std
import IterTree.Basic

namespace IterTree

namespace MpriRIP 
-- Obtained from https://gitlab.inria.fr/yzakowsk/mpri-2.4-rip/

inductive IOE : Type → Type where
  | Output (n : Nat) : IOE unit
  | Input : IOE nat

def aux_armes := (iTree.ret 1789 : iTree IOE Nat)

def double : iTree IOE Nat := do
  iTree.vis IOE.Input fun n => 
  iTree.ret <| 2 * n

def echo : iTree IOE Empty := do
  iTree.iter (init := ()) fun () =>
    iTree.vis IOE.Input fun n => 
    iTree.vis (IOE.Output n) fun () =>
    iTree.ret <| .inl ()

def spin_spec : iTree IOE Empty := iTree.loop

def spin : iTree E R := iTree.loop -- default

inductive FailEff : Type → Type where | intro : FailEff Empty

def fail : iTree FailEff R := .vis ⟨⟩ nofun

def seq (k : A → iTree E B) (u : iTree E A) := iTree.bindLeft k u

def bind (u : iTree E A) (k : A → iTree E B) := iTree.bindLeft k u

def trigger {E : Type _ → Type _} {A : Type _} (e : E A) : iTree E A :=
  iTree.vis e iTree.ret

def iter (step : I → iTree E (I ⊕ R)) init := iTree.iter step init

def NoEff : Type _ → Type _ := λ_↦Empty

def fact (n : Nat) : iTree NoEff Nat := 
  iTree.iter (init := (1,n)) fun
    | (acc, 0) => .ret <| .inr acc
    | (acc, n+1) => .ret <| .inl ((n+1)*acc, n)

def burn : Nat → iTree E R → iTree E R
  | 0, it => it
  | n+1, it => match it.unfold with 
    | .ret v => .ret v
    | .vis ev k => .vis ev k
    | .tau it => burn n it
      
#reduce burn 10 (fact 6)

def «repeat» (step : iTree E (Unit ⊕ Unit)) : iTree E Unit := 
  iter (λ_↦ step) ()

def interp_mrec {D E : Type _ → Type _}
  (ctx: ∀{X}, D X → iTree (λY↦ D Y ⊕ E Y) X) :
    ∀ {X: Type _}, iTree (λY↦D Y ⊕ E Y) X → iTree E X := 
  iTree.iter fun it =>
      match it.unfold with
      | .ret r => iTree.ret <| .inr r
      | .tau it => iTree.ret <| .inl it
      | .vis (.inl d) k => iTree.ret <| .inl (ctx d >>= k)
      | .vis (.inr e) k => iTree.vis e (.ret <| .inl <| k ·)

def mrec {D E : Type _ → Type _}
  (ctx: ∀{X}, D X → iTree (λY↦ D Y ⊕ E Y) X) :
    ∀ {X: Type _}, D X → iTree E X := 
  fun d => interp_mrec ctx (ctx d)

inductive CallEff (Arg Ret : Type _) : Type _ → Type _ where
  | call : Arg → CallEff Arg Ret Ret

def calling' (f : Arg → iTree F Ret) : ∀{X}, CallEff Arg Ret X → iTree F X
  | _, CallEff.call arg => f arg

def recur (body : Arg → iTree (λX↦ CallEff Arg Ret X ⊕ E X) Ret) :
    Arg → iTree E Ret
  | a => mrec (calling' body) (CallEff.call a)

def call {E : Type _ → Type _}(a : Arg) : iTree (λX↦ CallEff Arg Ret X ⊕ E X) Ret := 
  trigger (.inl <| .call a)

def fact_body (n : Nat) : iTree (λX↦ CallEff Nat Nat X ⊕ NoEff X) Nat := 
  match n with 
  | 0 => iTree.ret 1
  | n' + 1 => 
    (call n') >>= fun y =>
    iTree.ret (n * y)

def factorial (n : Nat) : iTree NoEff Nat :=
  recur (fact_body.{_,0}) n

#reduce burn 20 (factorial 6)

end MpriRIP
