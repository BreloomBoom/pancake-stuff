open bossLib;
open itreeTauTheory;
open relationTheory;
open pathTheory;
open arithmeticTheory;

val m = Hol_pp.print_apropos;
val f = Hol_pp.print_find;

Datatype:
  ffi = Send num | Recv | Qsize1 | Qsize2
End

Datatype:
  answer = Size num | Unit | Packet num
End

Inductive trans:
  trans (q1, q2) (SOME (Qsize1, Size (LENGTH q1))) (q1, q2) ∧
  trans (a::q1, q2) (SOME (Recv, Packet a)) (q1,q2) ∧
  trans (q1,q2) NONE (q1++[p], q2)
  ∧
  trans (q1, q2) (SOME (Qsize2, Size (LENGTH q2))) (q1, q2) ∧
  (LENGTH q2 < 5 ⇒ trans (q1, q2) (SOME (Send n, Unit)) (q1,q2 ++ [n])) ∧
  trans (q1, p::q2) NONE (q1, q2)
End
            
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
   (∀s'. weak_tau m s s' ⇒ ∃b s''. m s' (SOME(e,b)) s'') ∧
   (∀b s'. weak_trans m s (e,b) s' ⇒
           safe m s' (k b))
   ⇒ safe m s (Vis e k))
End

Definition get_no:
  get_no (Size x) = x ∧
  get_no (Packet x) = x
End

Definition rxdriver_def:
  rxdriver = itree_iter (λ_. Vis Qsize1
                                 (λx. Vis Qsize2
                                          (λy. if get_no x = 0 ∨ get_no y ≥ 5
                                               then Ret (INL ())
                                               else Vis Recv (λ(z : answer).
                                                                 Vis (Send (get_no z)) (λ_. Ret (INR ()))))))
                        ()
End

Theorem rxdriver:
  rxdriver = Vis Qsize1 (λx. Vis Qsize2 (λy.
             if get_no x = 0 ∨ get_no y ≥ 5 then Tau rxdriver
             else Vis Recv (λz. Vis (Send (get_no z)) (λ_. Ret ()))))
Proof
  rw[SimpL “$=”, rxdriver_def] >>
  gvs[Once itree_iter_thm, itree_bind_thm, FUN_EQ_THM] >>
  strip_tac >> strip_tac >>
  Cases_on ‘get_no x ≤ 0 ∨ get_no y >= 5’ >-
   (simp[rxdriver_def]) >>
  gvs[Once itree_iter_thm, itree_bind_thm, FUN_EQ_THM]
QED

    

Theorem increasing_q1:
  weak_tau trans s s' ⇒ LENGTH (FST s) ≤ LENGTH (FST s')
Proof
  fs[weak_tau_def] >>
  Induct_on ‘RTC’ >>
  rw[] >>
  subgoal ‘LENGTH (FST s) ≤ LENGTH (FST s')’
  >- (rw[trans_cases] >> fs[trans_cases]) >>
  gvs[]
QED

Theorem decreasing_q2_tau:
  weak_tau trans s s' ⇒ LENGTH (SND s) ≥ LENGTH (SND s')
Proof
  fs[weak_tau_def] >>
  Induct_on ‘RTC’ >>
  rw[] >>
  subgoal ‘LENGTH (SND s) ≥ LENGTH (SND s')’
  >- (rw[Once trans_cases] >> fs[trans_cases]) >>
  gvs[]
QED

Theorem decreasing_q2_trans:
  weak_trans trans s (Recv, b) s' ⇒ LENGTH (SND s') ≤ LENGTH (SND s) 
Proof
  rw[weak_trans_def] >>
  subgoal ‘LENGTH (SND s) ≥ LENGTH (SND s'') ∧ LENGTH (SND s'³') ≥ LENGTH (SND s')’
  >- gvs[decreasing_q2_tau] >>
  subgoal ‘LENGTH (SND s'') = LENGTH (SND s'³')’
  >- gvs[trans_cases] >> gvs[]
QED

Theorem increasing_q1_trans:
  weak_trans trans s (Qsize1, b) s' ⇒ get_no b ≤ LENGTH (FST s')
Proof
  rw[weak_trans_def] >>
  subgoal ‘LENGTH (FST s'³') ≤ LENGTH (FST s')’
  >- gvs[increasing_q1] >>
  subgoal ‘get_no b = LENGTH (FST s'³')’
  >- gvs[trans_cases, get_no] >> gvs[]
QED

Theorem Qsize2_trans:
  weak_trans trans s (Qsize2, b) s' ⇒ (get_no b ≥ LENGTH (SND s') ∧ LENGTH (FST s) ≤ LENGTH (FST s'))
Proof
  rw[]
  >- (gvs[Once weak_trans_def] >>
      subgoal ‘LENGTH (SND s'³') ≥ LENGTH (SND s')’
      >- gvs[decreasing_q2_tau] >>
      subgoal ‘get_no b = LENGTH (SND s'³')’
      >- gvs[trans_cases, get_no] >> gvs[])
  >- (gvs[Once weak_trans_def] >>
      subgoal ‘LENGTH (FST s) ≤ LENGTH (FST s'') ∧ LENGTH (FST s'³') ≤ LENGTH (FST s')’
      >- gvs[increasing_q1] >>
      subgoal ‘LENGTH (FST s'') = LENGTH (FST s'³')’
      >- gvs[trans_cases] >> gvs[])
QED

        
Theorem safe_driver:
  safe trans ([],[]) rxdriver
Proof
  irule safe_coind >>
  qexists_tac ‘λm s t. ∃q1 q2. m = trans ∧ s = (q1, q2) ∧
                           ((LENGTH q1 > 0 ∧ LENGTH q2 < 5 ∧
                             strip_tau t (Vis Recv (λz. Vis (Send (get_no z)) (λ_. Ret ())))) ∨
                           (LENGTH q2 < 5 ∧ ∃z. strip_tau t (Vis (Send z) (λ_. Ret ()))) ∨
                           (∃x.
                             strip_tau t (Ret ()) ∨ (* can be 5 now *)
                             strip_tau t rxdriver ∨
                             ((get_no x > 0 ⇒ LENGTH q1 > 0) ∧
                              strip_tau t (Vis Qsize2 (λy.
                                            if get_no x = 0 ∨ get_no y ≥ 5 then Tau rxdriver
                                            else Vis Recv (λz. Vis (Send (get_no z)) (λ_. Ret ())))))))’ >>
  rw[]
  >- (gvs[Once strip_tau_cases]
      >- (rw[] >> Cases_on ‘s'’ >> gvs[] >>
          drule increasing_q1 >> drule decreasing_q2_tau >> gvs[])
      >- (rw[]
          >- (Cases_on ‘s'’ >> Cases_on ‘q’
              >- (drule increasing_q1 >> rw[] >> gvs[])
              >- gvs[trans_cases])
          >- (Cases_on ‘s'’ >> rw[] >> drule decreasing_q2_trans >> gvs[])))
  >- (gvs[Once strip_tau_cases]
      >- (rw[] >> Cases_on ‘s'’ >> gvs[] >> disj2_tac >> disj1_tac >>
          drule decreasing_q2_tau >> rw[] >> qexists_tac ‘z’ >> gvs[])
      >- (conj_tac
          >- (rw[] >> drule decreasing_q2_tau >> Cases_on ‘s'’ >> gvs[trans_cases])
          >- (rw[] >> Cases_on ‘s'’ >> gvs[])))
  >- (gvs[Once strip_tau_cases] >> rw[] >> Cases_on ‘s'’ >> gvs[])
  >- (gvs[Once strip_tau_cases]
      >- (rw[] >> Cases_on ‘s'’ >> rw[] >> ntac 2 $ disj2_tac >> ntac 2 $ gvs[Once rxdriver] >>
          conj_tac >> rw[] >> Cases_on ‘s'’ >> gvs[trans_cases])
      >- (ntac 2 $ disj2_tac >> ntac 2 $ gvs[Once rxdriver] >>
          conj_tac >> rw[] >> Cases_on ‘s'’ >> gvs[trans_cases] >>
          qexists_tac ‘b’ >> gvs[] >> rw[] >> disj2_tac >>
          drule increasing_q1_trans >> gvs[]))
  >- (gvs[Once strip_tau_cases]
      >- (rw[] >> Cases_on ‘s'’ >> rw[] >> ntac 2 $ disj2_tac >> qexists_tac ‘x’ >> gvs[] >>
          rw[] >> ntac 2 $ disj2_tac >> drule increasing_q1 >> gvs[])
      >- (conj_tac
          >- (rw[] >> Cases_on ‘s'’ >> gvs[trans_cases])
          >- (rw[]
              >- (Cases_on ‘s'’ >> rw[] >> ntac 2 $ disj2_tac >>
                  qexists_tac ‘x’ >> disj2_tac >> disj1_tac >>
                  metis_tac[strip_tau_cases, rxdriver])
              >- (Cases_on ‘s'’ >> rw[] >> ntac 2 $ disj2_tac >>
                  qexists_tac ‘x’ >> disj2_tac >> disj1_tac >>
                  metis_tac[strip_tau_cases, rxdriver])
              >- (Cases_on ‘s'’ >> rw[] >> disj1_tac >>
                  drule Qsize2_trans >> gvs[]))))
  >- (disj2_tac >> qexists_tac ‘x’ >> disj2_tac >> disj1_tac >> metis_tac[strip_tau_cases, rxdriver])
QED
    


CoInductive is_path:
[~tau]
(∀s s' p i.
  is_path (pcons s' a p) i ∧
  trans s NONE s' ⇒
  is_path (pcons s NONE (pcons s' a p)) i)
[~action]
(∀s s' p e k.
  is_path (pcons s' a p) (k b) ∧
  trans s (SOME(e, b)) s' ⇒
  is_path (pcons s (SOME(e, b)) (pcons s' a p)) (Vis e k))
End

Definition head:
  head x p = (first p = x) 
End

Definition action:
  action s a s' p = (first p = s ∧ first_label p = a ∧ first (tail p) = s')
End

CoInductive always:
  (P (pcons s a p) ∧ G P p) ⇒ G P (pcons s a p)
End

Inductive eventually:
  (∀P p. P p ⇒ E P p) ∧
  (∀s a P p. E P p ⇒ E P (pcons s a p))
End

Inductive until:
 (∀P Q p. Q p ⇒ U P Q p) ∧
 (∀P Q s a p. (P (pcons s a p) ∧ U P Q p) ⇒ U P Q (pcons s a p))
End

Definition implication:
  I A B p = (A p ⇒ B p)
End    
    
CoInductive perp_enabled:
  ∀Tr p s s' a b c d. perp_enabled Tr (pcons c d p) ∧
                      (s, a, s') ∈ Tr ∧ trans s b c ⇒
                      perp_enabled Tr (pcons s b (pcons c d p))
End

Definition occurs:
  occurs Tr p = ∃s a s'. (s, a, s') ∈ Tr ∧ E (action s a s') p
End
  
Definition fairness:
  fair Tr p = G (I (perp_enabled Tr) (occurs Tr)) p
End


Theorem path_inf:
  ∀i. (is_path p i ⇒ ~(finite p))
Proof
  Induct_on ‘finite p’ using finite_path_ind >>
  rw[] >> rw[Once is_path_cases] >> simp[]
QED                                  
    
Theorem infinite_pcons:
  ~(finite p) ⇒ (∃a b c. p = pcons a b c)
Proof
  spose_not_then assume_tac >> rw[] >>
  ‘is_stopped p’ by (Cases_on ‘p’ using path_cases >> fs[]) >>
  gvs[finite_thm, is_stopped_def] 
QED

Theorem infinite_pcons1:
  ~(finite p) ∧ head ReadyS p ⇒ (∃b c d e. p = pcons ReadyS b (pcons c d e))
Proof
 rw[] >>
 ‘∃x y z. p = pcons x y z’ by (metis_tac[infinite_pcons]) >> fs[] >>
 ‘∃r s t. z = pcons r s t’ by (metis_tac[infinite_pcons]) >> fs[head]
QED

Theorem is_path_rsdriver_cases:
  (is_path (pcons a b' c) (rsdriver:(bool,label,'a) itree) ∨
   is_path (pcons a b' c) ((Vis Send (λb. rsdriver)):(bool,label,'a) itree)) ⇒
  (is_path c (rsdriver:(bool,label,'a) itree) ∨
   is_path c ((Vis Send (λb. rsdriver)):(bool,label,'a) itree))
Proof
  rw[] >>
  qhdtm_x_assum `is_path` mp_tac >>
  rw[Once is_path_cases] >> simp[] >>
  pop_assum kall_tac >>
  gvs[Once rsdriver] >>                     
  Cases_on ‘b’ >> fs[]
QED

Theorem fair_pcons:
  fair {(ReadyS,SOME (Send,T),UnreadyS)} (pcons a b' c) ⇒
  fair {(ReadyS,SOME (Send,T),UnreadyS)} c
Proof
  rw[Once always_cases, fairness]
QED
    
Theorem not_UnreadyS:
  (is_path (pcons a b c) (rsdriver:(bool,label,'a) itree) ∨
   is_path (pcons a b c) ((Vis Send (λx. rsdriver)):(bool,label,'a) itree)) ∧
  head ReadyS (pcons a b c) ∧
  ¬E (action ReadyS (SOME(Send, T)) UnreadyS) (pcons a b c) ⇒
  perp_enabled {(ReadyS, SOME(Send, T), UnreadyS)} (pcons a b c)
Proof
  rw[] >>
  irule perp_enabled_coind >>
  qexists_tac ‘λs t. s = {(ReadyS, SOME(Send, T), UnreadyS)} ∧
                     head ReadyS t ∧
                     ¬E (action ReadyS (SOME(Send, T)) UnreadyS) t ∧
                     (is_path t (rsdriver:(bool,label,'a) itree) ∨
                      is_path t ((Vis Send (λx. rsdriver)):(bool,label,'a) itree))’ >>
  rw[] >>
  ntac 3 $ pop_last_assum kall_tac >>
  ‘∃p q r s. a1 = pcons ReadyS p (pcons q r s)’ by (metis_tac[path_inf, infinite_pcons1]) >>
  gvs[head] >>
  irule_at Any is_path_rsdriver_cases >> qexistsl_tac [‘p’, ‘ReadyS’] >> simp[] >>
  fs[Once eventually_cases, Once is_path_cases] >>
  gvs[trans_cases, action]
QED

Theorem live_rsdriver:
  is_path p rsdriver ∧ fair {(ReadyS, SOME(Send, T), UnreadyS)} p ⇒
  G (I (head ReadyS) (E (action ReadyS (SOME(Send, T)) UnreadyS))) p 
Proof
  rw[] >>
  irule always_coind >>
  qexists_tac ‘{ p | (is_path p (rsdriver:(bool,label,'a) itree) ∨
                      is_path p ((Vis Send (λb. rsdriver)):(bool,label,'a) itree)) ∧
                     fair {(ReadyS, SOME(Send, T), UnreadyS)} p }’ >> rw[] >>
  ntac 2 (pop_last_assum kall_tac) >>
  ‘∃a b c. a0 = pcons a b c’ by (metis_tac[path_inf, infinite_pcons]) >>
  fs[implication] >>
  irule_at Any is_path_rsdriver_cases >> qexistsl_tac [‘b’, ‘a’] >> simp[] >>
  irule_at Any fair_pcons >> qexistsl_tac [‘b’, ‘a’] >> simp[] >>
  rw[] >> fs[fairness] >>
  Cases_on ‘perp_enabled {(ReadyS, SOME(Send, T), UnreadyS)} (pcons a b c)’
  >- (gvs[Once always_cases, implication, occurs] >> rw[])
  >- (metis_tac[not_UnreadyS])
  >- (gvs[Once always_cases, implication, occurs] >> rw[])
  >- (metis_tac[not_UnreadyS])
QED

