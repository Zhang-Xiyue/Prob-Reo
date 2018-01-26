(*==========timed data distribution stream========*)
Require Import Reals.
Require Import Streams.
Require Export Utheory.

Open Scope type_scope.
Definition Time := R.
Definition Data := nat. 
Definition DataDist := Data * U.
Definition TDD := Time * DataDist.
Definition PrL {A B: Type}(pair: A  * B) :=
  match pair with
  | (a, b) => a
  end.
Definition PrR {A B: Type}(pair: A * B ) :=
  match pair with
  | (a, b) => b
  end.

(*increasing time moments*)
Open Scope R_scope.
Axiom Inc_T : forall (T: Stream TDD)(n:nat),
  PrL(Str_nth n T) < PrL(Str_nth n (tl T)).


(*=============judgement===========*)

       (*the judgement about time*)
                 (*Basic:*)
Definition Teq(s1 s2:Stream TDD) : Prop :=
  forall n:nat, PrL(Str_nth n s1) = PrL(Str_nth n s2).
Definition Tlt(s1 s2:Stream TDD) : Prop :=
  forall n:nat, PrL(Str_nth n s1) < PrL(Str_nth n s2).
Definition Tgt(s1 s2:Stream TDD) : Prop :=
  forall n:nat, PrL(Str_nth n s1) > PrL(Str_nth n s2).
                  (*Timed:*)
Definition Teqt(s1 s2:Stream TDD)(t:Time) : Prop :=
  forall n:nat, PrL(Str_nth n s1) + t = PrL(Str_nth n s2).
Definition Tltt(s1 s2:Stream TDD)(t:Time) : Prop :=
  forall n:nat, PrL(Str_nth n s1) + t < PrL(Str_nth n s2).
Definition Tgtt(s1 s2:Stream TDD)(t:Time) : Prop :=
  forall n:nat, PrL(Str_nth n s1) + t > PrL(Str_nth n s2).
       (*the judgement about data*)
Definition Deq(s1 s2:Stream TDD) : Prop :=
  forall n:nat, PrR(Str_nth n s1) = PrR(Str_nth n s2).
(*==============channel=============*)
Open Scope U_scope.
                         (*Basic channel*)
Definition Sync(Input Output:Stream TDD) : Prop :=
  Input = Output. (*i.e. Teq Input Output /\ Deq Input Output*)
Definition SyncDrain(Input1 Input2:Stream TDD) : Prop :=
  (Teq Input1 Input2).
Definition FIFO1(Input Output:Stream TDD) : Prop :=
  (Tlt Input Output)
  /\
  (Tlt Output (tl Input))
  /\
  (Deq Input Output).
Fixpoint FIFO (n:nat)(s1 s2:Stream TDD):Prop:= 
  match n with
  |0 => FIFO1 s1 s2
  |S m => exists s3:Stream TDD, (FIFO m s1 s3) /\ (FIFO1 s3 s2)
  end.
Definition FIFO1e(Input Output:Stream TDD) (e:Data) : Prop :=
  (Tgt Input Output)
  /\
  PrR(hd Output)=(e,1)
  /\
  (Deq Input (tl Output)).
Parameter AsyncDrain : Stream TDD -> Stream TDD -> Prop.
Axiom AsyncDrain_coind:
  forall Input1 Input2:Stream TDD,
  AsyncDrain Input1 Input2 ->
  (
      (~PrL(hd Input1)  =  PrL (hd Input2))
  )
  /\
  (
      (   (PrL(hd Input1)  <  PrL (hd Input2))
          /\
          AsyncDrain (tl Input1) Input2               )
      /\
      (   (PrL(hd Input1)  >  PrL (hd Input2))
          /\
          AsyncDrain Input1 (tl Input2)               )
  ).
Parameter LossySync : Stream TDD -> Stream TDD -> Prop.
Axiom LossySync_coind:
  forall Input Output:Stream TDD,
  LossySync Input Output ->
  (
    (hd Output = hd Input  /\  LossySync (tl Input) (tl Output))
    \/
    LossySync (tl Input) Output
  ).
                      (*Timed channel*)
Parameter timeout : Data.
Definition Timert (Input Output:Stream TDD)(t:Time) : Prop :=
  (forall n:nat, PrL(Str_nth n Input) + t  < PrL(Str_nth n (tl Input)))
  /\
  (Teqt Input Output t)
  /\
  (forall n:nat, PrR (Str_nth n Output) = (timeout, 1)).
Open Scope R_scope.
Parameter off : Data.
Parameter OFFTimert : Stream TDD -> Stream TDD -> Time -> Prop.
Axiom OFFTimert_coind:
  forall (Input Output:Stream TDD)(t:Time), OFFTimert Input Output t ->

  (     forall n:nat, PrR(Str_nth n Input) = (off, 1%U)  \/ PrL(Str_nth n Input) + t  < PrL(Str_nth n (tl Input))
  )/\
  (    (PrR (hd (tl Input)) = (off, 1%U))   -> (OFFTimert (tl (tl Input)) Output t)
  )/\
  (    (~PrR (hd (tl Input)) = (off, 1%U)) -> (PrL (hd Output) = (PrL (hd Input)) + t)  /\
                                                   (PrR (hd Output) = (timeout,1%U))                /\
                                                   OFFTimert (tl Input) (tl Output) t
  ).

Parameter reset : Data.
Parameter RSTTimert : Stream TDD -> Stream TDD -> Time -> Prop.
Axiom RSTTimert_coind:
  forall (Input Output:Stream TDD)(t:Time), RSTTimert Input Output t ->

  (     forall n:nat, PrR(Str_nth n Input) = (reset, 1%U)  \/ PrL(Str_nth n Input) + t  < PrL(Str_nth n (tl Input))
  )/\
  (    (PrR (hd (tl Input)) = (reset, 1%U))   -> (RSTTimert  (tl Input) Output t)  
  )/\
  (    (~PrR (hd (tl Input)) = (reset, 1%U)) -> (PrL (hd Output) = PrL (hd Input) + t) /\
                                                      (PrR (hd Output) = (timeout, 1%U))               /\
                                                      RSTTimert (tl Input) (tl Output) t
  ).

Parameter expire : Data.
Parameter EXPTimert : Stream TDD -> Stream TDD -> Time -> Prop.
Axiom EXPTimert_coind:
  forall (Input Output:Stream TDD)(t:Time), EXPTimert Input Output t ->

  (     forall n:nat, PrR(Str_nth n Input) = (expire,1%U)  \/ PrL(Str_nth n Input) + t  < PrL(Str_nth n (tl Input))
  )/\
  (    (PrR(hd (tl Input)) = (expire, 1%U))   -> (PrL(hd Output) = PrL(hd (tl Input))) /\
                                                       (PrR(hd Output) = (timeout, 1%U))             /\
                                                       (EXPTimert (tl Input) (tl Output) t)
  )/\
  (    (~PrR(hd (tl Input)) = (expire, 1%U)) -> (PrL (hd Output) = PrL (hd Input) + t) /\
                                                       (PrR (hd Output) = (timeout, 1%U))               /\
                                                       (EXPTimert (tl Input) (tl Output) t)
  ).

(*==============probabilistic channel=============*)
Open Scope U_scope.
Parameter c : Data.
Parameter CptSync : Stream TDD -> Stream TDD -> U -> Prop.
Axiom CptSync_coind:
  forall (Input Output:Stream TDD) (p:U),
  CptSync Input Output p -> 
  ( PrL(hd Output) = PrL (hd Input) 
  /\
    (  
       PrR(hd Output) = (c, [1-] (([1-] p) * (PrR(PrR(hd Input)))))
    \/ PrR(hd Output) = (PrL(PrR(hd Input)), ([1-] p) * (PrR(PrR(hd Input))))
    )
  /\
    CptSync (tl Input) (tl Output) p
  ).

Definition RdmSync(Input Output:Stream TDD):Prop :=
  (forall n:nat, PrR (Str_nth n Output) = (1%nat, [1/]1+1) \/
  PrR (Str_nth n Output) = (O%nat, [1/]1+1))
  /\ Teq Input Output.

Parameter ProbLossy : Stream TDD -> Stream TDD -> U -> Prop.
Axiom ProbLossy_coind:
  forall (Input Output:Stream TDD) (q:U),
  ProbLossy Input Output q ->
  (
    (PrL(hd Output) = PrL(hd Input) /\ 
     PrR(hd Output) = (PrL(PrR(hd Input)), PrR(PrR(hd Input)) * ([1-] q))  /\  
     ProbLossy (tl Input) (tl Output) q)
    \/
    ProbLossy (tl Input) Output q
  ).

Parameter FtyFIFO1 : Stream TDD -> Stream TDD -> U -> Prop.
Axiom  FtyFIFO1_coind:
  forall (Input Output:Stream TDD) (r:U),
  FtyFIFO1 Input Output r -> 
  (
    (PrL(hd Output) > PrL(hd Input) /\ 
     PrL(hd Output) < PrL(hd (tl Input)) /\
     PrR(hd Output) = (PrL(PrR(hd Input)), PrR(PrR(hd Input)) * ([1-] r)) /\
     FtyFIFO1 (tl Input) (tl Output) r)
     \/
    FtyFIFO1 (tl Input) Output r
  ).

(*=============Operators============*)
Parameter merge : Stream TDD -> Stream TDD ->Stream TDD -> Prop.
Axiom merge_coind:
  forall s1 s2 s3:Stream TDD, merge s1 s2 s3 ->
  (   ~(PrL(hd s1) = PrL(hd s2))
  /\
  (
     (   (PrL(hd s1) < PrL(hd s2))  -> ( (hd s3=hd s1)  /\ merge (tl s1) s2 (tl s3))   )
     /\
     (   (PrL(hd s1) > PrL(hd s2))  -> ( (hd s3=hd s2)  /\ merge s1 (tl s2) (tl s3))   )
  ) ).

(*example 2*)
Section Example2.
Open Scope R_scope.
(*Auxiliary definition and lemma*)
Definition t_FIFO1 (M N:Stream TDD) (t:Time):Prop :=
  exists R S:Stream TDD, 
  (FIFO1 M R) /\ (SyncDrain R S) /\ (Timert M S t) /\ (Sync R N).

Variable t:Time.
Variables M N R S D C:Stream TDD.
(*Lemma tFIFO1_eq: (t_FIFO1 M N t) <->  exists (R S:Stream TDD),
  (FIFO1 M R) /\ (SyncDrain R S) /\ (Timert M S t) /\ (Sync R N).
Proof.
split.
intro.
auto.
intro.
auto.
Qed.*)

Variable E: Stream TDD.

Lemma RSync_tFIFO_eq: forall (A B: Stream TDD) (t:Time),  exists E: Stream TDD, 
     (RdmSync A E) /\ (t_FIFO1 E B t) 
     <->
     (RdmSync A E) /\ (exists (D C:Stream TDD), (FIFO1 E D)  /\ (SyncDrain D C) /\ (Timert E C t) /\ (Sync D B)).
Proof.
intros A B t0.
exists E.
split.

(* proof for ->*)
intros.
destruct H.
split.
assumption.
auto.

(* proof for <-*)
intros.
destruct H.
split.
assumption.
auto.
Qed.

Lemma tFIFO_RSync_eq: forall (A B: Stream TDD) (t:Time), exists E: Stream TDD,
     (t_FIFO1 A E t) /\ (RdmSync E B) 
     <->
     (exists (D C:Stream TDD), (FIFO1 A D)  /\ (SyncDrain D C) /\ (Timert A C t) /\ (Sync D E)) /\ (RdmSync E B).
Proof.
intros A B t0.
exists E.
split.

(* proof for ->*)
intros.
destruct H.
split.
auto.
assumption.

(* proof for <-*)
intros.
destruct H.
split.
auto.
assumption.
Qed.

Lemma transfer_dist: forall (A B : Stream TDD),
     (forall n:nat, PrR (Str_nth n A) = (1%nat, ([1/]1+1)%U) \/ PrR (Str_nth n A) = (O, ([1/]1+1)%U))
  /\ Deq A B  -> 
     (forall n:nat, PrR (Str_nth n B) = (1%nat, ([1/]1+1)%U) \/ PrR (Str_nth n B) = (O, ([1/]1+1)%U)).
Proof.
intros.
destruct H.
assert (Deq A B -> (forall n:nat, PrR(Str_nth n A) = PrR(Str_nth n B))).
auto.
assert (forall n:nat, PrR(Str_nth n A) = PrR(Str_nth n B)).
apply H1.
assumption.
rewrite <- H2.
generalize n.
assumption.
Qed.

Lemma trans_t_eq: forall (s1 s2 s3:Stream TDD)(t:Time), 
   (Teqt s1 s2 t) /\ (Teqt s1 s3 t) -> (Teq s2 s3).
Proof.
intros.
destruct H.
assert (forall n:nat, PrL(Str_nth n s1) + t0  = PrL(Str_nth n s2)).
auto.
assert (forall n:nat, PrL(Str_nth n s1) + t0  = PrL(Str_nth n s3)).
auto.
assert (forall n:nat, PrL(Str_nth n s2)  = PrL(Str_nth n s3)).
intro.
rewrite <- H1.
auto.
auto.
Qed.

Lemma trans_eq_t: forall (s1 s2 s3:Stream TDD)(t:Time), 
   (Teqt s1 s3 t) /\ (Teqt s2 s3 t) -> (Teq s1 s2).
Proof.
intros.
destruct H.
assert (forall n:nat, PrL(Str_nth n s1) + t0  = PrL(Str_nth n s3)).
auto.
assert (forall n:nat, PrL(Str_nth n s2) + t0  = PrL(Str_nth n s3)).
auto.
assert (forall n:nat, PrL(Str_nth n s1) + t0 = PrL(Str_nth n s2) + t0).
intro.
rewrite H1.
rewrite H2.
reflexivity.
assert (forall n:nat, (PrL(Str_nth n s1) + t0 = PrL(Str_nth n s2) + t0)
         -> (PrL(Str_nth n s1) = PrL(Str_nth n s2))).
admit.
assert (forall n:nat, PrL(Str_nth n s1) = PrL(Str_nth n s2)).
intro.
apply H4.
apply H3.
auto.
Qed.

Hypothesis tFIFO1_eq: forall (A B:Stream TDD) (t:Time), t_FIFO1 A B t <-> (Deq A B) /\ (Teqt A B t).
Variables A B A_t B_t: Stream TDD.
Hypothesis transfer_eqt : forall (s1 s2 s3:Stream TDD)(t:Time),
   (Teq s1 s2) /\ (Teqt s2 s3 t) -> (Teqt s1 s3 t).
Hypothesis transfer_R_eqt : forall (s1 s2 s3:Stream TDD)(t:Time),
   (Teq s2 s3) /\ (Teqt s1 s2 t) -> (Teqt s1 s3 t).
Hypothesis A_R_t: Deq A A_t /\ Teqt A A_t t.
Hypothesis B_R_t: Deq B_t B /\ Teqt B_t B t.

Theorem equivalence: forall (A B:Stream TDD) (t:Time),
  (exists E, (RdmSync A E) /\ (t_FIFO1 E B t))
<->
  (exists R, (t_FIFO1 A R t) /\ (RdmSync R B)).
Proof.
intro.
split.

(*proof for ->*)
intros.
assert (R=A_t).
admit.
exists R.
rewrite H0.
split.
(*proof for t_FIFO1 A A_t t*)
apply tFIFO1_eq.
split.
destruct A_R_t.
assert (A0=A).
admit.
rewrite H3.
assumption.
destruct A_R_t.
assert (A0=A).
admit.
rewrite H3.
assert (t0=t).
admit.
rewrite H4.
assumption.
(*proof for RdmSync A_t B*)
destruct H as [E0].
destruct H.
split.
destruct H.
assert (t_FIFO1 E0 B0 t0 -> (Deq E0 B0) /\ (Teqt E0 B0 t0)).
apply tFIFO1_eq.
assert (Deq E0 B0 /\ Teqt E0 B0 t0).
apply H3.
assumption.
destruct H4.
assert ((forall n : nat, PrR (Str_nth n E0) = (1%nat, [1/]1+1) \/ PrR (Str_nth n E0) = (0%nat, [1/]1+1))
      /\ Deq E0 B0 -> 
       (forall n : nat, PrR (Str_nth n B0) = (1%nat, [1/]1+1) \/ PrR (Str_nth n B0) = (0%nat, [1/]1+1))).
apply transfer_dist.
apply H6.
split.
assumption.
assumption.

destruct H.
assert (t_FIFO1 E0 B0 t0 -> (Deq E0 B0) /\ (Teqt E0 B0 t0)).
apply tFIFO1_eq.
assert (Deq E0 B0 /\ Teqt E0 B0 t0).
apply H3.
assumption.
destruct H4.
assert ((Teq A0 E0) /\ (Teqt E0 B0 t0) -> (Teqt A0 B0 t0)).
apply transfer_eqt.
assert (Teqt A0 B0 t0).
apply H6.
split.
assumption.
assumption.
destruct A_R_t.
assert ((Teqt A A_t t) /\ (Teqt A B0 t) -> (Teq A_t B0)).
apply trans_t_eq.
apply H10.
split.
assumption.
assert (A=A0).
admit.
rewrite H11.
assert (t=t0).
admit.
rewrite H12.
assumption.

(*proof for <-*)
intros.
assert (E=B_t).
admit.
exists E.
rewrite H0.
split.
(*proof for RdmSync A B_t*)
destruct H as [R0].
destruct H.
split.
destruct H1.
destruct B_R_t.
assert ((forall n : nat, PrR (Str_nth n B0) = (1%nat, [1/]1+1) \/ PrR (Str_nth n B0) = (0%nat, [1/]1+1))
      /\ Deq B0 B_t -> 
       (forall n : nat, PrR (Str_nth n B_t) = (1%nat, [1/]1+1) \/ PrR (Str_nth n B_t) = (0%nat, [1/]1+1))).
apply transfer_dist.
apply H5.
split.
assumption.
assert (B0=B).
admit.
rewrite H6.
assert (forall n:nat, PrR(Str_nth n B_t) = PrR(Str_nth n B)).
auto.
assert (forall n:nat, PrR(Str_nth n B) = PrR(Str_nth n B_t)).
intro.
rewrite H7.
reflexivity.
auto.

assert (t_FIFO1 A0 R0 t0 -> (Deq A0 R0) /\ (Teqt A0 R0 t0)).
apply tFIFO1_eq.
assert (Deq A0 R0 /\ Teqt A0 R0 t0).
apply H2.
assumption.
destruct H3.
destruct H1.
assert ((Teq R0 B0) /\ (Teqt A0 R0 t0) -> (Teqt A0 B0 t0)).
apply transfer_R_eqt.
assert (Teqt A0 B0 t0).
apply H6.
split.
assumption.
assumption.
destruct B_R_t.
assert ((Teqt A B t) /\ (Teqt B_t B t) -> (Teq A B_t)).
apply trans_eq_t.
assert (A0=A).
admit.
rewrite H11.
apply H10.
split.
rewrite <- H11.
assert (B0=B).
admit.
rewrite <- H12.
assert (t0=t).
admit.
rewrite <- H13.
assumption.
assumption.
(*proof for t_FIFO1 B_t B t*)
apply tFIFO1_eq.
split.
destruct B_R_t.
assert (B0=B).
admit.
rewrite H3.
assumption.
destruct B_R_t.
assert (B0=B).
admit.
rewrite H3.
assert (t0=t).
admit.
rewrite H4.
assumption.
Qed.
End Example2.
