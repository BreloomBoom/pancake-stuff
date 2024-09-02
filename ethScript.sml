open itreeTauTheory;
open relationTheory;
open pathTheory;
open arithmeticTheory;
open finite_mapTheory;

val m = Hol_pp.print_apropos;
val f = Hol_pp.print_find;

Definition weak_tau_def:
  weak_tau m = RTC (λs s'. m s NONE s')
End

Definition weak_trans_def:
  weak_trans m s e s' =
  (∃s'' s'''.
     weak_tau m s s'' ∧
     m s'' (SOME e) s''' ∧
     weak_tau m s''' s')
End

CoInductive safe:
[~ret]
  (∀s r m. safe m s (Ret r))
[~tau]
  (∀s t m. (∀s'. weak_tau m s s' ⇒ safe m s' t) ⇒
   safe m s (Tau t))
[~vis]
  (∀e k s m.
   (∀s'. weak_tau m s s' ⇒ ∃b s''. m s' (SOME(e,b)) s'') ∧ (* not stuck in s *)
   (∀b s'. weak_trans m s (e,b) s' ⇒ safe m s' (k b))      (* all steps valid *)
   ⇒ safe m s (Vis e k))
End

(* driver modelled on tx_provide path, very similar to rx_provide (- signals)
   two pointers: head chases --> tail, head inclusive not tail
   it may only update tail on queue 2 (hardware), head on queue 1 (OS)
 *)

Definition qmax_def:
  QMAX = 256
End

Datatype:
  ethq = <| hd : num ; tl : num ; ps : num |-> num |>
End

(* in future, store queue locations in the state,
   check addresses with respect to these

   note: some transitions apply to invalid states. However we never reach
   invalid states from valid ones

   |... hd -> || ACTIVE REGION || <- tl, exclusive ...|
   |... ACTIVE || <- tl excl. ...  hd -> || ACTIVE ...|
 *)

Definition in_q1:
  in_q1 q n = (n ≥ q.hd ∧ n < q.tl)
End

Definition in_q2:
  in_q2 q n = ((q.hd MOD QMAX ≤ n ∧ n < q.tl MOD QMAX) ∨
                  (q.tl MOD QMAX < q.hd MOD QMAX ∧
                   (n < q.tl MOD QMAX ∨ q.hd ≤ n MOD QMAX)))
End

(* ALL active entries in the queue must be initialized *)
Definition q1wf:
  q1wf q = (q.hd ≤ q.tl ∧ q.tl - q.hd ≤ QMAX ∧ ∀n. in_q1 q n ⇒ n ∈ FDOM q.ps)
End

Definition q2wf:
  q2wf q = (q.hd < QMAX ∧ q.tl < QMAX ∧ ∀n. in_q2 q n ⇒ n ∈ FDOM q.ps)
End

Datatype:
  ffi = Pop num | Push num | Read num | Write num num
      | Head1 | Tail1 | Head2 | Tail2
End

Datatype:
  answer = Addr num | Unit
End

Definition get_no:
  get_no (Addr n) = n
End

    
(* in future, store queue locations in the state,
   check addresses with respect to these

   note: some transitions apply to invalid states. However we never reach
   invalid states from valid ones
 *)
Inductive eth:
  (* read hd/tl values *)
  (eth (q1, q2) (SOME (Head1, Addr q1.hd)) (q1, q2)) ∧
  (eth (q1, q2) (SOME (Head2, Addr q2.hd)) (q1, q2)) ∧
  (eth (q1, q2) (SOME (Tail1, Addr q1.tl)) (q1, q2)) ∧
  (eth (q1, q2) (SOME (Tail2, Addr q2.tl)) (q1, q2)) ∧
       
  (* read from q1 *)
  ((in_q1 q1 n) ⇒ eth (q1, q2) (SOME (Read n, Addr (THE (FLOOKUP q1.ps n)))) (q1, q2)) ∧

  (* write to q2 *)
  ((¬in_q2 q2 n) ⇒ eth (q1, q2) (SOME (Write n p, Unit)) (q1, q2 with ps := q2.ps |+ (n, p))) ∧

  (* set hd/tl *)
  (in_q1 q1 n
   ⇒ eth (q1, q2) (SOME (Pop n, Unit)) (q1 with hd := n, q2)) ∧
  
  ((¬in_q2 q2 n ∧ (∀i. in_q2 (q2 with tl := n) i ⇒ i ∈ FDOM q2.ps) ∧ n < QMAX)
   ⇒ eth (q1,q2) (SOME (Push n, Unit)) (q1, q2 with tl := n)) ∧

  (* device enqueue to q1 and dequeue from q2 *)
  (q1.tl - q1.hd < QMAX
   ⇒ eth (q1, q2) NONE ((q1 with ps := q1.ps |+ (q1.tl, n))
                            with tl := q1.tl + 1, q2)) ∧
  (q2.tl - q2.hd > 0
   ⇒ eth (q1, q2) NONE (q1, q2 with hd := (q2.hd + 1) MOD QMAX))
End

Theorem qsoundness:
  q1wf q1 ∧ q2wf q2 ∧ eth (q1, q2) e (q1', q2') ⇒ (q1wf q1' ∧ q2wf q2')
Proof
  rw[q1wf, q2wf, eth_cases] >> gvs[in_q1, in_q2] >>
  Cases_on ‘n' < q1.tl’ >> gvs[]
QED
    
