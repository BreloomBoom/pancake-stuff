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
  in_q2 q n = ((q.hd ≤ n ∧ n < q.tl) ∨
               (q.tl < q.hd ∧ (n < q.tl ∨ (q.hd ≤ n ∧ n < QMAX))))
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
  answer = num
End
    
(* in future, store queue locations in the state,
   check addresses with respect to these

   note: some transitions apply to invalid states. However we never reach
   invalid states from valid ones
 *)
Inductive eth:
  (* read hd/tl values *)
  (eth (q1, q2) (SOME (Head1, q1.hd)) (q1, q2)) ∧
  (eth (q1, q2) (SOME (Head2, q2.hd)) (q1, q2)) ∧
  (eth (q1, q2) (SOME (Tail1, q1.tl)) (q1, q2)) ∧
  (eth (q1, q2) (SOME (Tail2, q2.tl)) (q1, q2)) ∧
       
  (* read from q1 *)
  ((in_q1 q1 n) ⇒ eth (q1, q2) (SOME (Read n, THE (FLOOKUP q1.ps n))) (q1, q2)) ∧

  (* write to q2 *)
  ((¬in_q2 q2 n) ⇒ eth (q1, q2) (SOME (Write n p, 0)) (q1, q2 with ps := q2.ps |+ (n, p))) ∧

  (* set hd/tl *)
  (in_q1 q1 n ∨ n = q1.tl
   ⇒ eth (q1, q2) (SOME (Pop n, 0)) (q1 with hd := n, q2)) ∧
  
  ((¬in_q2 q2 n ∧ (∀i. in_q2 (q2 with tl := n) i ⇒ i ∈ FDOM q2.ps) ∧ n < QMAX)
   ⇒ eth (q1,q2) (SOME (Push n, 0)) (q1, q2 with tl := n)) ∧

  (* device enqueue to q1 and dequeue from q2 *)
  (q1.tl - q1.hd < QMAX
   ⇒ eth (q1, q2) NONE ((q1 with ps := q1.ps |+ (q1.tl, n))
                            with tl := q1.tl + 1, q2)) ∧
  (q2.tl ≠ q2.hd
   ⇒ eth (q1, q2) NONE (q1, q2 with hd := (q2.hd + 1) MOD QMAX))
End

(* proving that queues are well formed after transitioning *)
    
Theorem soundness:
  q1wf q1 ∧ q2wf q2 ∧ eth (q1, q2) e (q1', q2') ⇒ (q1wf q1' ∧ q2wf q2')
Proof
  rw[q1wf, q2wf, eth_cases] >> gvs[in_q1, in_q2]
  >- (Cases_on ‘n' < q1.tl’ >> gvs[]) >>
  Cases_on ‘q2.tl < q2.hd’ >> gvs[] >>
  Cases_on ‘q2.hd < QMAX - 1’ >> gvs[] >>
  ‘q2.hd + 1 = QMAX’ by gvs[] >> gvs[]
QED

Theorem weak_tau_soundness:
  q1wf q ∧ q2wf r ∧ weak_tau eth (q, r) (q', r') ⇒ q1wf q' ∧ q2wf r'
Proof
  fs[weak_tau_def] >>
  qid_spec_tac ‘q’ >> qid_spec_tac ‘r’ >> 
  Induct_on ‘RTC’ >>
  rw[] >> gvs[] >>
  Cases_on ‘r'³'’ >> 
  ‘q1wf q'' ∧ q2wf r''’ by metis_tac[soundness] >>
  gvs[]
QED
    
Theorem weak_trans_soundness:
  q1wf q1 ∧ q2wf q2 ∧ weak_trans eth (q1, q2) e (q1', q2') ⇒ q1wf q1' ∧ q2wf q2'
Proof
  fs[weak_trans_def] >>
  strip_tac >>
  Cases_on ‘s'³'’ >> Cases_on ‘s''’ >>
  ‘q1wf q' ∧ q2wf r'’ by metis_tac[weak_tau_soundness] >>
  ‘q1wf q ∧ q2wf r’ by metis_tac[soundness] >>
  metis_tac[weak_tau_soundness]
QED

Definition length_q1:
  length_q1 q1 = q1.tl - q1.hd
End              
    
Definition length_q2:
  length_q2 q2 = if q2.tl ≥ q2.hd then q2.tl - q2.hd else QMAX + q2.tl - q2.hd
End

    
(* alternate length_q2: (QMAX + q2.tl - q2.hd) MOD QMAX *)

    
Definition rxdriver:
  rxdriver = Vis Head2 (λx. Vis Tail2
        (λy. Vis Head1 (λz. Vis Tail1
                                (λw.
                                   if (w - z = 0 ∨ ((QMAX + y - x + 1) MOD QMAX) = 0)
                                   then Ret ()
                                   else Vis (Read z)
                                   (λa. Vis (Pop (z + 1))
                                            (λ_. Vis (Write y a)
                                            (λ_. Vis (Push ((y + 1) MOD QMAX))
                                                     (λ_. Ret ()))))))))
End

(* (incomplete) proofs without a notion of length

Theorem none_q2_hd:
  q2wf (SND s) ∧ q2wf (SND s') ∧ eth s NONE ⇒
  (SND s).hd = (SND s').hd ∨ ((SND s).hd + 1) MOD QMAX = (SND s').hd ∧ (SND s).hd ≠ (SND s').tl)  
Proof
  Cases_on ‘s’ >> Cases_on ‘s'’ >> rw[] >>
  gvs[Once eth_cases, q2wf]
QED
    
Theorem weak_tau_q2_hd:
  q1wf q1 ∧ q2wf q2 ∧ q2wf q2' ∧ weak_tau eth (q1,q2) (q1',q2')
  ⇒ (in_q2 (q2' with hd := q2.hd) q2'.hd ∨
     q2'.hd = q2'.tl)
Proof
  ‘∀q1 q2 q1' q2'. weak_tau eth (q1,q2) (q1',q2') ⇒ q2.tl = q2'.tl’
  by metis_tac[weak_tau_eq, pairTheory.SND] >>
  gvs[weak_tau_def] >>
  qid_spec_tac ‘q2’ >> qid_spec_tac ‘q1’ >> 
  Induct_on ‘RTC’ >>
  rw[] >> gvs[in_q2] >>
  pop_assum mp_tac >> Cases_on ‘q2'³'’ >> gvs[] >> rw[] >>
  ‘q1wf q ∧ q2wf r’ by metis_tac[soundness] >>
  ‘q2.hd = r.hd ∨ (q2.hd + 1) MOD QMAX = r.hd ∧ q2.hd ≠ r.tl’
    by metis_tac[none_q2_hd, pairTheory.SND] >> gvs[] >>
  Cases_on ‘q2.hd < QMAX - 1’ >> gvs[q2wf]
  >- (Cases_on ‘q2'.tl < QMAX - 1’ >> gvs[] >>
      ‘q2.hd = q2'.tl’ by gvs[] >>
      ‘r.tl = q2'.tl’ by metis_tac[] >> gvs[])
  >- (Cases_on ‘q2'.tl < q2.hd’ >> gvs[] >>
      ‘q2'.tl = q2.hd’ by gvs[] >>
      ‘q2'.tl = r.tl’ by metis_tac[] >> gvs[])
  >- (Cases_on ‘q2'.tl < q2.hd’ >> gvs[] >>
      ‘q2'.tl = q2.hd’ by gvs[] >>
      ‘q2'.tl = r.tl’ by metis_tac[] >> gvs[])
  >- (‘q2.hd = QMAX - 1’ by gvs[q2wf] >>
      ‘r.hd = 0’ by gvs[q2wf] >> gvs[])
QED

Theorem weak_trans_head2:
  q1wf q1' ∧ q2wf q2' ∧ q2wf r ∧ weak_trans eth (q1', q2') (Head2, b) (q, r)
  ⇒ (in_q2 (r with hd := b) r.hd ∨ r.hd = r.tl)
Proof
  rw[Once weak_trans_def] >>
  Cases_on ‘s''’ >> Cases_on ‘s'³'’ >>
  irule weak_tau_q2_hd >>
  ‘q1wf (FST (q1', q2')) ∧ q2wf (SND (q1', q2')) ∧ weak_tau eth (q1', q2') (q', r')
   ⇒ (q1wf (FST (q', r')) ∧ q2wf (SND (q', r')))’
    by metis_tac[weak_tau_soundness] >> gvs[] >>
  ‘q1wf q'' ∧ q2wf r''’ by metis_tac[soundness] >> metis_tac[]
QED

Theorem weak_tau_in_q2_hd:
  in_q2 (q2 with hd := x) q2.hd ∧ weak_tau eth (q1, q2) (q, r) ∧
  q1wf q1' ∧ q2wf q2' ∧ q1wf q ∧ q2wf r ⇒
  in_q2 (r with hd := x) r.hd ∨ r.hd = r.tl
Proof
  fs[weak_tau_def] >>
  qid_spec_tac ‘q2’ >> qid_spec_tac ‘q1’ >> 
  Induct_on ‘RTC’ >> rw[] >> gvs[in_q2]
  >- ()
QED
    
Theorem weak_trans_tail2:
  in_q2 (q2' with hd := x) q2'.hd ∧ weak_trans eth (q1', q2') (Tail2, b) (q, r) ∧
  q1wf q1 ∧ q2wf q2 ∧ q1wf q1' ∧ q2wf q2'∧ q1wf q ∧ q2wf r ⇒
  in_q2 (r with hd := x) r.hd ∨ r.hd = r.tl
Proof
  rw[weak_trans_def] >>
  Cases_on ‘s''’ >> Cases_on ‘s'³'’ >>
  ‘q'' = q' ∧ r'' = r'’ by gvs[eth_cases] >> gvs[] >>
QED *)

(* proofs about length notions *)

Theorem weak_tau_eq:
  weak_tau eth (q, r) (q', r') ⇒ r.tl = r'.tl ∧ q.hd = q'.hd
Proof
  fs[weak_tau_def] >>
  qid_spec_tac ‘q’ >> qid_spec_tac ‘r’ >>
  Induct_on ‘RTC’ >> rw[] >>
  Cases_on ‘r'³'’ >>
  qpat_x_assum ‘_꙳ _ _’ kall_tac >>
  gvs[eth_cases]
QED
   
(* theorems about q2 length and with hd *)

Theorem none_length_with_hd:
  eth (q, r) NONE (q', r') ⇒ length_q2 (r' with hd := r.hd) = length_q2 r
Proof
  rw[] >>
  ‘r.tl = r'.tl’ by fs[eth_cases] >>
  gvs[eth_cases, length_q2]
QED
    
Theorem weak_tau_length_with_hd:
  weak_tau eth (q, r) (q', r') ⇒ length_q2 (r' with hd := r.hd) = length_q2 r
Proof
  fs[weak_tau_def] >>
  qid_spec_tac ‘q'’ >> qid_spec_tac ‘r'’ >>
  Induct_on ‘RTC’ using RTC_INDUCT_RIGHT1 >>
  rw[] >- gvs[length_q2] >>
  Cases_on ‘s’ >>
  ‘r'.tl = r''.tl’ by fs[eth_cases] >>
  gvs[length_q2]          
QED

(* theorems about how q2 length changes with transitions *)
    
Theorem none_length_q2:
  q2wf q2 ∧ q2wf q2' ∧ eth (q1, q2) NONE (q1', q2') ⇒
  length_q2 q2 = length_q2 q2' ∨ length_q2 q2 = length_q2 q2' + 1
Proof
  rw[q2wf, length_q2] >> gvs[eth_cases] >>
  Cases_on ‘q2.hd < QMAX - 1’ >> gvs[] >>
  ‘q2.hd + 1 = QMAX’ by rw[] >> gvs[]
QED

Theorem weak_tau_length_q2:
  weak_tau eth (q, r) (q', r') ∧
  q1wf q' ∧ q2wf r' ∧ q1wf q ∧ q2wf r
  ⇒ length_q2 r ≥ length_q2 r'
Proof
  fs[weak_tau_def] >>
  qid_spec_tac ‘q’ >> qid_spec_tac ‘r’ >>
  Induct_on ‘RTC’ >> rw[] >- rw[] >>
  Cases_on ‘r'³'’ >>
  ‘q1wf q'' ∧ q2wf r''’ by metis_tac[soundness] >> gvs[] >>
  ‘length_q2 r = length_q2 r'' ∨ length_q2 r = length_q2 r'' + 1’
    by metis_tac[none_length_q2] >> gvs[]
QED
    
Theorem weak_trans_length_head2:
  weak_trans eth (q1, q2) (Head2, b) (q, r) ∧
  q1wf q1 ∧ q2wf q2 ∧ q1wf q ∧ q2wf r
  ⇒ length_q2 (r with hd := b) ≥ length_q2 r
Proof
  rw[weak_trans_def] >> Cases_on ‘s''’ >>
  ‘s'³' = (q', r') ∧ b = r'.hd’ by gvs[eth_cases] >>
  ‘q1wf q' ∧ q2wf r'’ by metis_tac[weak_tau_soundness] >>
  metis_tac[weak_tau_length_q2, weak_tau_length_with_hd]
QED

Theorem weak_trans_length_rest:
  e ∈ {Tail2; Head1; Tail1; Read a} ∧
  length_q2 (q2' with hd := x) ≥ length_q2 q2' ∧
  weak_trans eth (q1', q2') (e, b) (q, r) ∧
  q1wf q1' ∧ q2wf q2' ∧ q1wf q ∧ q2wf r
  ⇒ length_q2 (r with hd := x) ≥ length_q2 r
Proof
  rw[weak_trans_def] >> Cases_on ‘s''’ >>
  ‘s'³' = (q', r')’ by gvs[eth_cases] >>
  ‘q1wf q' ∧ q2wf r'’ by metis_tac[weak_tau_soundness] >>
  ‘r'.tl = r.tl ∧ q2'.tl = r'.tl’ by metis_tac[weak_tau_eq] >>
  ‘length_q2 (q2' with hd := x) = length_q2 (r with hd := x)’ by gvs[length_q2] >>
  ‘length_q2 q2' ≥ length_q2 r' ∧ length_q2 r' ≥ length_q2 r’
    by metis_tac[weak_tau_length_q2] >>
  rw[]
QED

(* theorems about constant values from function calls *)

Theorem tail_2:
  weak_trans eth (q, r) (Tail2, b) (q', r') ⇒ r'.tl = b
Proof
  rw[weak_trans_def] >>
  Cases_on ‘s'³'’ >>
  ‘r'.tl = r''.tl’ by metis_tac[weak_tau_eq] >>
  gvs[eth_cases]
QED

Theorem head_1:
  weak_trans eth (q, r) (Head1, b) (q', r') ⇒ b = q'.hd
Proof
  rw[weak_trans_def] >>
  Cases_on ‘s'³'’ >>
  ‘s'' = (q'', r'')’ by gvs[eth_cases] >> rw[] >>
  ‘b = q''.hd’ by gvs[eth_cases] >>
  ‘q''.hd = q'.hd’ by metis_tac[weak_tau_eq] >> gvs[]
QED
    
Theorem weak_trans_eq:
  e ∈ {Head1; Head2; Tail1; Tail2; Read a} ∧
  weak_trans eth (q, r) (e, b) (q', r')
  ⇒ q.hd = q'.hd ∧ r.tl = r'.tl                                                    
Proof
  rw[weak_trans_def] >>
  Cases_on ‘s'³'’ >>
  ‘s'' = (q'', r'')’ by gvs[eth_cases] >> rw[] >>
  ‘r'.tl = r''.tl ∧ r.tl = r''.tl ∧ q'.hd = q''.hd ∧ q.hd = q''.hd’
  by metis_tac[weak_tau_eq] >> gvs[]
QED

(* theorems about q1 *)

Theorem weak_tau_q1_tl:
  weak_tau eth (q, r) (q', r') ⇒ q.tl ≤ q'.tl
Proof
  fs[weak_tau_def] >>
  qid_spec_tac ‘q’ >> qid_spec_tac ‘r’ >>
  Induct_on ‘RTC’ >> rw[] >- rw[] >>
  Cases_on ‘r'³'’ >>
  qpat_x_assum ‘_꙳ _ _’ kall_tac >>
  gvs[eth_cases]
QED               
  
Theorem tail_1:
  weak_trans eth (q, r) (Tail1, b) (q', r') ⇒ b ≤ q'.tl
Proof
  rw[weak_trans_def] >>
  Cases_on ‘s'³'’ >>
  ‘b = q''.tl’ by gvs[eth_cases] >>
  ‘q''.tl ≤ q'.tl’ by metis_tac[weak_tau_q1_tl] >>          
  simp[]
QED
    
Theorem weak_trans_q1_tl:
  e ∈ {Read a} ∧ weak_trans eth (q, r) (e, b) (q', r') ⇒ q.tl ≤ q'.tl
Proof
  rw[weak_trans_def] >>
  Cases_on ‘s'³'’ >>
  ‘s'' = (q'', r'')’ by gvs[eth_cases] >> rw[] >>
  ‘q.tl ≤ q''.tl ∧ q''.tl ≤ q'.tl’ by metis_tac[weak_tau_q1_tl] >>
  simp[]
QED

(* for popping *)

Theorem pop_q2_tl:
  weak_trans eth (q, r) (Pop (q.hd + 1), b) (q', r') ⇒ r.tl = r'.tl
Proof
  rw[weak_trans_def] >> Cases_on ‘s'³'’ >> Cases_on ‘s''’ >>
  ‘r'³' = r''’ by gvs[eth_cases] >> rw[] >>
  ‘r.tl = r''.tl ∧ r''.tl = r'.tl’ by metis_tac[weak_tau_eq] >> simp[]
QED

Theorem pop_q1_tl:
  weak_trans eth (q, r) (Pop (q.hd + 1), b) (q', r') ⇒ q.tl ≤ q'.tl
Proof
  rw[weak_trans_def] >> Cases_on ‘s'³'’ >> Cases_on ‘s''’ >>
  ‘q.tl ≤ q'³'.tl ∧ q''.tl ≤ q'.tl’ by metis_tac[weak_tau_q1_tl] >>
  ‘q'³'.tl ≤ q''.tl’ by gvs[eth_cases] >> simp[]
QED
    
Theorem pop_q2_length:
  length_q2 (r with hd := x) ≥ length_q2 r ∧
  weak_trans eth (q, r) (Pop (q.hd + 1), b) (q', r') ∧
  q1wf q ∧ q2wf r ∧ q1wf q' ∧ q2wf r'
  ⇒ length_q2 (r' with hd := x) ≥ length_q2 r'
Proof
  rw[weak_trans_def] >> Cases_on ‘s''’ >> Cases_on ‘s'³'’ >>
  ‘r'³' = r''’ by gvs[eth_cases] >> rw[] >>
  ‘q1wf q'' ∧ q2wf r''’ by metis_tac[weak_tau_soundness] >>
  ‘q1wf q'³'’ by metis_tac[soundness] >>
  ‘r''.tl = r.tl ∧ r''.tl = r'.tl’ by metis_tac[weak_tau_eq] >>
  ‘length_q2 (r' with hd := x) = length_q2 (r with hd := x)’ by gvs[length_q2] >>          
  ‘length_q2 r ≥ length_q2 r'' ∧ length_q2 r'' ≥ length_q2 r'’
    by metis_tac[weak_tau_length_q2] >> rw[]
QED

(* for pushing *)

Theorem push_tl:
  weak_trans eth (q, r) (Write x y, b) (q', r') ⇒ r.tl = r'.tl ∧ q.tl ≤ q'.tl
Proof
  rw[weak_trans_def] >> Cases_on ‘s''’ >> Cases_on ‘s'³'’
  >- (‘r''.tl = r'³'.tl’ by gvs[eth_cases] >>
      ‘r''.tl = r.tl ∧ r''.tl = r'.tl’ by metis_tac[weak_tau_eq] >> simp[])
  >- (‘q'' = q'³'’ by gvs[eth_cases] >>
      ‘q.tl ≤ q''.tl ∧ q''.tl ≤ q'.tl’ by metis_tac[weak_tau_q1_tl] >> simp[])     
QED
    
Theorem push_q2_length:
  length_q2 (r with hd := x) ≥ length_q2 r ∧
  weak_trans eth (q, r) (Write n m, b) (q', r') ∧
  q1wf q ∧ q2wf r ∧ q1wf q' ∧ q2wf r'
  ⇒ length_q2 (r' with hd := x) ≥ length_q2 r'
Proof
  rw[weak_trans_def] >> Cases_on ‘s''’ >> Cases_on ‘s'³'’ >>
  ‘r'³'.tl = r''.tl ∧ r'³'.hd = r''.hd’ by gvs[eth_cases] >> rw[] >>
  ‘q1wf q'' ∧ q2wf r''’ by metis_tac[weak_tau_soundness] >>
  ‘q1wf q'³' ∧ q2wf r'³'’ by metis_tac[soundness] >>
  ‘r''.tl = r.tl ∧ r''.tl = r'.tl’ by metis_tac[weak_tau_eq] >>
  ‘length_q2 (r' with hd := x) = length_q2 (r with hd := x)’ by gvs[length_q2] >>          
  ‘length_q2 r ≥ length_q2 r'' ∧ length_q2 r'³' ≥ length_q2 r'’
    by metis_tac[weak_tau_length_q2] >>
  ‘length_q2 r'' = length_q2 r'³'’ by metis_tac[length_q2] >> simp[]
QED

(* random domain stuff for the final cases *)
    
Theorem weak_tau_dom:
  weak_tau eth (q', r') (q, r) ∧ a ∈ FDOM r'.ps ⇒ a ∈ FDOM r.ps
Proof
  fs[weak_tau_def] >>
  qid_spec_tac ‘r'’ >> qid_spec_tac ‘q'’ >>
  Induct_on ‘RTC’ >> rw[] >- rw[] >>
  Cases_on ‘r'³'’ >> rw[] >>
  ‘a ∈ FDOM r''.ps’ by gvs[eth_cases] >> simp[]
QED
    
Theorem write_dom:
  weak_trans eth (q1', q2') (Write r.tl a, b) (q, r)
  ⇒ r.tl ∈ FDOM r.ps
Proof
  rw[weak_trans_def] >> Cases_on ‘s'³'’ >> Cases_on ‘s''’ >>
  ‘r.tl ∈ FDOM r'.ps’ by gvs[eth_cases] >>
  metis_tac[weak_tau_dom]
QED

(* oh god its more length theorems *)

Theorem max_length_q2:
  q2wf q ⇒ length_q2 q < QMAX
Proof
  gvs[length_q2, q2wf]
QED

Theorem head2_max_length:
  weak_trans eth (q, r) (Head2, b) (q', r') ∧ q1wf q ∧ q2wf r
  ⇒ QMAX > length_q2 (r' with hd := b)
Proof
  rw[weak_trans_def] >>
  Cases_on ‘s'³'’ >>
  ‘s'' = (q'', r'')’ by gvs[eth_cases] >>
  ‘b = r''.hd’ by gvs[eth_cases] >>
  ‘r''.tl = r'.tl’ by metis_tac[weak_tau_eq] >>
  ‘length_q2 (r' with hd := r''.hd) = length_q2 r''’ by gvs[length_q2] >>
  ‘q2wf r''’ by metis_tac[weak_tau_soundness] >> gvs[] >>
        drule max_length_q2 >> simp[]
QED
    
Theorem remaining_max_length:
  e ∈ {Tail2; Head1; Tail1; Read a; Write n m; Pop c} ∧
  QMAX > length_q2 (r with hd := x) ∧
  weak_trans eth (q, r) (e, b) (q', r')
  ⇒ QMAX > length_q2 (r' with hd := x)
Proof
  rw[weak_trans_def] >>
  Cases_on ‘s'³'’ >> Cases_on ‘s''’ >>
  ‘r''.tl = r'³'.tl’ by gvs[eth_cases] >>
  ‘r.tl = r'³'.tl ∧ r''.tl =  r'.tl’ by metis_tac[weak_tau_eq] >>
  gvs[length_q2]
QED
     
Theorem weak_tau_not_in_q2:
  q1wf q ∧ q2wf r ∧
  QMAX > length_q2 (r with hd := x) ∧
  weak_tau eth (q, r) (q', r') ∧
  length_q2 (r with hd := x) ≥ length_q2 r ∧
  (QMAX + r.tl - x + 1) MOD QMAX ≠ 0
  ⇒ ¬in_q2 r' ((r.tl + 1) MOD QMAX)
Proof
  rw[] >>
  ‘r.tl = r'.tl’ by metis_tac[weak_tau_eq] >>
  ‘q1wf q' ∧ q2wf r'’ by metis_tac[weak_tau_soundness] >>
  ‘length_q2 r ≥ length_q2 r'’ by metis_tac[weak_tau_length_q2] >>
  Cases_on ‘r.tl + 1 < QMAX’ >> gvs[q2wf, in_q2]
  >- (Cases_on ‘¬(r'.tl < r'.hd) ∨ ¬(r'.hd ≤ r'.tl + 1)’ >> gvs[] >>
      ‘r'.hd = r'.tl + 1’ by gvs[] >>
      subgoal ‘length_q2 r' = QMAX - 1’
      >- gvs[length_q2] >>
      ‘length_q2 (r with hd := x) = QMAX - 1’ by gvs[] >>
      Cases_on ‘r'.tl ≥ x’ >> gvs[length_q2])
  >- (‘r'.tl + 1 = QMAX’ by gvs[] >> 
      Cases_on ‘¬(r'.hd ≤ (r'.tl + 1) MOD QMAX) ∨ ¬((r'.tl + 1) MOD QMAX < r'.tl)’ >>
      gvs[] >>
      ‘length_q2 r' = QMAX - 1’ by gvs[length_q2] >>
      ‘length_q2 (r with hd := x) = QMAX - 1’ by gvs[] >>
      Cases_on ‘r'.tl ≥ x’ >> gvs[length_q2] >>
      ‘x = 0’ by gvs[] >> gvs[])
QED

Theorem in_q2_plus_1:
  length_q2 r < QMAX - 1 ∧ q2wf r ∧
  in_q2 (r with tl := (r.tl + 1) MOD QMAX) i
  ⇒ in_q2 r i ∨ i = r.tl
Proof
  rw[] >>
  gvs[in_q2, q2wf, length_q2] >>
  Cases_on ‘r.tl + 1 = QMAX’ >> gvs[]
QED
    
Theorem weak_tau_in_q2_dom:
  length_q2 r < QMAX - 1 ∧
  r.tl ∈ FDOM r.ps ∧ q2wf r ⇒
  (∀i. in_q2 (r with tl := (r.tl + 1) MOD QMAX) i ⇒ i ∈ FDOM r.ps)
Proof
  rw[] >>
  ‘in_q2 r i ∨ i = r.tl’ by metis_tac[in_q2_plus_1] >>
  gvs[q2wf]
QED
  
Theorem weak_tau_in_in_q2:
  length_q2 r < QMAX - 1 ∧
  in_q2 (r' with tl := (r.tl + 1) MOD QMAX) i ∧
  weak_tau eth (q, r) (q', r') ∧ q2wf r ∧ q2wf r' ∧ q1wf q ∧ q1wf q' 
  ⇒ in_q2 (r with tl := (r.tl + 1) MOD QMAX) i
Proof
  rw[] >>
  ‘r.tl = r'.tl’ by metis_tac[weak_tau_eq] >> gvs[] >>
  ‘length_q2 r ≥ length_q2 r'’ by metis_tac[weak_tau_length_q2] >>
  rw[in_q2, q2wf] >> gvs[length_q2] >>
  Cases_on ‘r'.tl + 1 = QMAX’ >>
  Cases_on ‘r'.tl ≥ r.hd’ >> gvs[in_q2, q2wf]
QED  

Theorem q2_inherit:
  length_q2 r < QMAX - 1 ∧
  weak_tau eth (q, r) (q', r') ∧
  q2wf r ∧ q2wf r' ∧ q1wf q ∧ q1wf q' ∧                                      
  (∀i. in_q2 (r with tl := (r.tl + 1) MOD QMAX) i ⇒ i ∈ FDOM r.ps)
  ⇒ (∀i. in_q2 (r' with tl := (r.tl + 1) MOD QMAX) i ⇒ i ∈ FDOM r'.ps)
Proof
  rw[] >> metis_tac[weak_tau_in_in_q2, weak_tau_dom]
QED   

Theorem not_max_length:
  QMAX > length_q2 (r with hd := x) ∧
  length_q2 (r with hd := x) ≥ length_q2 r ∧
  (QMAX + r.tl - x + 1) MOD QMAX ≠ 0 ∧ q2wf r
  ⇒ length_q2 r < QMAX - 1
Proof
  rw[] >>
  Cases_on ‘length_q2 r < QMAX - 1’ >> simp[] >>
  ‘length_q2 (r with hd := x) = QMAX - 1’ by gvs[] >>
  gvs[q2wf] 
  >- (Cases_on ‘r.tl ≥ x’
      >- (‘QMAX + r.tl - x + 1 = 2 * QMAX’ by gvs[length_q2] >> gvs[])
      >- fs[length_q2])
  >- (Cases_on ‘r.tl ≥ x’
      >- (‘QMAX + r.tl - x + 1 = 2 * QMAX’ by gvs[length_q2] >> gvs[])
      >- fs[length_q2])
QED


Theorem rxdriver_safe:
  q1wf q1 ∧ q2wf q2 ⇒ safe eth (q1, q2) rxdriver
Proof
  rw[] >>
  irule safe_coind >>
  qexists_tac ‘λm s t. ∃q1' q2'. q1wf q1' ∧ q2wf q2' ∧ m = eth ∧ s = (q1', q2') ∧
                             (t = rxdriver ∨ t = Ret () ∨
                              (∃x. length_q2 (q2' with hd := x) ≥ length_q2 q2' ∧
                                   QMAX > length_q2 (q2' with hd := x) ∧
                              t = Vis Tail2 (λy. Vis Head1 (λz. Vis Tail1 (λw.
                                  if (w - z = 0 ∨ ((QMAX + y - x + 1) MOD QMAX) = 0)
                                  then Ret ()
                                  else Vis (Read z) (λa. Vis (Pop (z + 1))
                                  (λ_. Vis (Write y a) (λ_. Vis (Push ((y + 1) MOD QMAX))
                                                                (λ_. Ret ())))))))) ∨
                              (∃x. length_q2 (q2' with hd := x) ≥ length_q2 q2' ∧
                                   QMAX > length_q2 (q2' with hd := x) ∧
                              t = Vis Head1 (λz. Vis Tail1 (λw.
                                  if (w - z = 0 ∨ ((QMAX + q2'.tl - x + 1) MOD QMAX) = 0)
                                  then Ret ()
                                  else Vis (Read z) (λa. Vis (Pop (z + 1))
                                  (λ_. Vis (Write q2'.tl a) (λ_. Vis (Push ((q2'.tl + 1) MOD QMAX))
                                                                     (λ_. Ret ()))))))) ∨
                              (∃x. length_q2 (q2' with hd := x) ≥ length_q2 q2' ∧
                                   QMAX > length_q2 (q2' with hd := x) ∧
                              t = Vis Tail1 (λw.
                                  if (w - q1'.hd = 0 ∨ ((QMAX + q2'.tl - x + 1) MOD QMAX) = 0)
                                  then Ret ()
                                  else Vis (Read q1'.hd) (λa. Vis (Pop (q1'.hd + 1))
                                  (λ_. Vis (Write q2'.tl a) (λ_. Vis (Push ((q2'.tl + 1) MOD QMAX))
                                                                     (λ_. Ret ())))))) ∨
                              (∃x w. length_q2 (q2' with hd := x) ≥ length_q2 q2' ∧
                                     QMAX > length_q2 (q2' with hd := x) ∧
                                     (w ≤ q1'.tl) ∧
                              t = if (w - q1'.hd = 0 ∨ ((QMAX + q2'.tl - x + 1) MOD QMAX) = 0)
                                  then Ret ()
                                  else Vis (Read q1'.hd) (λa. Vis (Pop (q1'.hd + 1))
                                  (λ_. Vis (Write q2'.tl a) (λ_. Vis (Push ((q2'.tl + 1) MOD QMAX))
                                                                     (λ_. Ret ()))))) ∨
                              (∃x w. length_q2 (q2' with hd := x) ≥ length_q2 q2' ∧
                                     QMAX > length_q2 (q2' with hd := x) ∧
                                     (w ≤ q1'.tl) ∧
                                   ¬(w - q1'.hd = 0 ∨ ((QMAX + q2'.tl - x + 1) MOD QMAX) = 0) ∧
                              t = Vis (Read q1'.hd) (λa. Vis (Pop (q1'.hd + 1))
                             (λ_. Vis (Write q2'.tl a) (λ_. Vis (Push ((q2'.tl + 1) MOD QMAX))
                                                                (λ_. Ret ()))))) ∨
                              (∃x w a. length_q2 (q2' with hd := x) ≥ length_q2 q2' ∧
                                       QMAX > length_q2 (q2' with hd := x) ∧
                                       (w ≤ q1'.tl) ∧
                                       ¬(w - q1'.hd = 0 ∨ ((QMAX + q2'.tl - x + 1) MOD QMAX) = 0) ∧
                              t = Vis (Pop (q1'.hd + 1))
                             (λ_. Vis (Write q2'.tl a) (λ_. Vis (Push ((q2'.tl + 1) MOD QMAX))
                                                                (λ_. Ret ())))) ∨
                              (∃x w a. length_q2 (q2' with hd := x) ≥ length_q2 q2' ∧
                                       QMAX > length_q2 (q2' with hd := x) ∧
                                       (w ≤ q1'.tl) ∧
                                       ¬(((QMAX + q2'.tl - x + 1) MOD QMAX) = 0) ∧
                              t = Vis (Write q2'.tl a) (λ_. Vis (Push ((q2'.tl + 1) MOD QMAX))
                                                                (λ_. Ret ()))) ∨
                              (∃x w a. length_q2 (q2' with hd := x) ≥ length_q2 q2' ∧
                                       QMAX > length_q2 (q2' with hd := x) ∧
                                       (w ≤ q1'.tl) ∧
                                       ¬(((QMAX + q2'.tl - x + 1) MOD QMAX) = 0) ∧
                                       q2'.tl ∈ FDOM q2'.ps ∧
                              t = Vis (Push ((q2'.tl + 1) MOD QMAX))
                                      (λ_. Ret ())))’ >>
  rw[]
  >- (rpt $ disj2_tac >> rw[Once rxdriver] >>
      Cases_on ‘s'’ >> gvs[eth_cases] >>
      ‘q1wf q ∧ q2wf r’ by metis_tac[weak_trans_soundness] >> rw[] >>
      disj2_tac >> disj1_tac >> qexists ‘b’ >> gvs[] >>
      metis_tac[weak_trans_length_head2, head2_max_length])
  >- (rw[] >> Cases_on ‘s'’ >> gvs[eth_cases] >>
      ‘q1wf q ∧ q2wf r’ by metis_tac[weak_trans_soundness] >> rw[] >>
      disj2_tac >> disj1_tac >> qexists ‘x’ >> gvs[] >> rw[]
      >- (irule weak_trans_length_rest >> fs[] >> metis_tac[]) >>
      ‘b = r.tl’ by metis_tac[tail_2] >> gvs[] >>
      irule remaining_max_length >> fs[] >> metis_tac[])
  >- (rw[] >> Cases_on ‘s'’ >> gvs[eth_cases] >>
      ‘q1wf q ∧ q2wf r’ by metis_tac[weak_trans_soundness] >> rw[] >>
      disj2_tac >> disj1_tac >> qexists ‘x’ >> gvs[] >> rw[]
      >- (irule weak_trans_length_rest >> fs[] >>  metis_tac[]) >>
      ‘b = q.hd’ by metis_tac[head_1] >>
      subgoal ‘q1'.hd = q.hd ∧ q2'.tl = r.tl’
      >- (irule weak_trans_eq >> fs[] >> metis_tac[]) >> gvs[]
      >- (irule remaining_max_length >> fs[] >> metis_tac[]) >>
      irule weak_trans_eq >> fs[] >> metis_tac[])
  >- (rw[] >> Cases_on ‘s'’ >> gvs[eth_cases] >>
      ‘q1wf q ∧ q2wf r’ by metis_tac[weak_trans_soundness] >> rw[] >>
      rpt $ disj2_tac >> qexistsl [‘x’, ‘b’] >> rw[]
      >- (irule weak_trans_length_rest >> fs[] >> metis_tac[])
      >- (irule remaining_max_length >> fs[] >> metis_tac[]) >>
      subgoal ‘q1'.hd = q.hd ∧ q2'.tl = r.tl’
      >- (irule weak_trans_eq >> fs[] >> metis_tac[]) >> gvs[]                                                 
      >- metis_tac[tail_1] >>
      irule weak_trans_eq >> fs[] >> metis_tac[])
  >- (Cases_on ‘w ≤ q1'.hd ∨ (QMAX + q2'.tl − x + 1) MOD QMAX = 0’ >> gvs[] >>
      rw[] >> Cases_on ‘s'’ >> gvs[eth_cases]
      >- (‘q.hd = q1'.hd’ by metis_tac[weak_tau_eq] >>
          ‘q1'.tl ≤ q.tl’ by metis_tac[weak_tau_q1_tl] >> gvs[in_q1]) >>
      ‘q1wf q ∧ q2wf r’ by metis_tac[weak_trans_soundness] >> rw[] >>
      rpt $ disj2_tac >> qexistsl [‘x’, ‘w’, ‘b’] >>
      subgoal ‘QMAX > length_q2 (r with hd := x)’
      >- (irule remaining_max_length >> fs[] >> metis_tac[]) >> simp[] >>
      subgoal ‘q1'.hd = q.hd ∧ q2'.tl = r.tl’
      >- (irule weak_trans_eq >> fs[] >> metis_tac[]) >> gvs[] >> rw[]
      >- (irule weak_trans_length_rest >> fs[] >> metis_tac[]) >>
      subgoal ‘q1'.tl ≤ q.tl’
      >- (irule weak_trans_q1_tl >> fs[] >> metis_tac[]) >> simp[])
  >- (rw[] >> Cases_on ‘s'’ >> gvs[eth_cases]
      >- (‘q.hd = q1'.hd’ by metis_tac[weak_tau_eq] >>  
          ‘q1'.tl ≤ q.tl’ by metis_tac[weak_tau_q1_tl] >> gvs[in_q1]) >>
      ‘q1wf q ∧ q2wf r’ by metis_tac[weak_trans_soundness] >> rw[] >>
      rpt $ disj2_tac >> qexistsl [‘x’, ‘w’, ‘b’] >>
      subgoal ‘QMAX > length_q2 (r with hd := x)’
      >- (irule remaining_max_length >> fs[] >> metis_tac[]) >> simp[] >>
      subgoal ‘q1'.hd = q.hd ∧ q2'.tl = r.tl’
      >- (irule weak_trans_eq >> fs[] >> metis_tac[]) >> gvs[] >> rw[]
      >- (irule weak_trans_length_rest >> fs[] >> metis_tac[]) >>
      subgoal ‘q1'.tl ≤ q.tl’
      >- (irule weak_trans_q1_tl >> fs[] >> metis_tac[]) >> simp[])
  >- (rw[] >> Cases_on ‘s'’ >> gvs[eth_cases]
      >- (Cases_on ‘q1'.hd + 1 = q.tl’ >> gvs[in_q1] >>
          ‘q1'.hd = q.hd’ by metis_tac[weak_tau_eq] >>
          ‘q1'.tl ≤ q.tl’ by metis_tac[weak_tau_q1_tl] >> gvs[]) >>
      ‘q1wf q ∧ q2wf r’ by metis_tac[weak_trans_soundness] >> rw[] >>
      rpt $ disj2_tac >> qexistsl [‘x’, ‘w’] >>
      subgoal ‘QMAX > length_q2 (r with hd := x)’
      >- (irule remaining_max_length >> fs[] >> metis_tac[]) >> simp[] >>
      ‘q2'.tl = r.tl’ by metis_tac[pop_q2_tl] >> fs[] >>
      ‘q1'.tl ≤ q.tl’ by metis_tac[pop_q1_tl] >> simp[] >>
      metis_tac[pop_q2_length])
  >- (rw[] >> Cases_on ‘s'’ >> gvs[eth_cases]
      >- (‘r.tl = q2'.tl’ by metis_tac[weak_tau_eq] >> gvs[in_q2]) >>
      ‘q1wf q ∧ q2wf r’ by metis_tac[weak_trans_soundness] >> rw[] >>
      rpt $ disj2_tac >> qexistsl [‘x’, ‘w’] >>
      subgoal ‘QMAX > length_q2 (r with hd := x)’
      >- (irule remaining_max_length >> fs[] >> metis_tac[]) >> simp[] >>
      ‘q2'.tl = r.tl ∧ q1'.tl ≤ q.tl’ by metis_tac[push_tl] >> fs[] >>
      metis_tac[push_q2_length, write_dom])
  >- (rw[] >> Cases_on ‘s'’ >> gvs[eth_cases]
      >- (‘¬in_q2 r ((q2'.tl + 1) MOD QMAX)’ by metis_tac[weak_tau_not_in_q2] >> simp[] >>
          ‘length_q2 q2' < QMAX - 1’ by metis_tac[not_max_length] >>
          ‘q1wf q ∧ q2wf r’ by metis_tac[weak_tau_soundness] >> 
          metis_tac[weak_tau_in_q2_dom, q2_inherit]) >>
      ‘q1wf q ∧ q2wf r’ by metis_tac[weak_trans_soundness] >> rw[])       
QED
