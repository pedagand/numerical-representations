
Require Import Arith.
Require Import Lia.
Open Scope nat_scope.
Require Import List.
Import ListNotations.

(* List Utils *)
(* to be moved elsewhere*)

Lemma app_eq_app_helper : forall A (l l1 l0 : list A), 
l ++ l1 = l ++ l0 -> l1 = l0.
Proof.
  intros A l l1 l0 H0.
  apply app_eq_app in H0. destruct H0 as [l2 Hyp]. 
  destruct Hyp as [[Hyp1 Hyp2] | [Hyp1 Hyp2]]; apply (@f_equal (list A) _ (@length A)) in Hyp1 ;
  rewrite app_length in Hyp1; assert (length l2 = 0) as Hp by lia ;
  rewrite length_zero_iff_nil in Hp ; rewrite Hp in Hyp2 ; auto.
Qed.

Lemma app_eq_app_helper3 : forall A (l l1 l0 : list A), 
l1 ++ l = l0 ++ l -> l1 = l0.
Proof.
  intros A l l1 l0 H0.
  apply (@f_equal (list A) _ (@rev A)) in H0. 
  do 2 (rewrite rev_app_distr in H0).
  apply app_eq_app_helper in H0.
  apply (@f_equal (list A) _ (@rev A)) in H0. 
  do 2 (rewrite rev_involutive in H0) ; assumption.
Qed.


Lemma app_eq_app_helper2 : forall A (l l1 l2 l0 : list A), 
l0 ++ l1 = l2 ++ l -> length l0 = length l2 -> l1 = l.
Proof.
  intros A l l1 l2 l0 H0 H.
  apply app_eq_app in H0. destruct H0 as [l3 Hyp]. 
  destruct Hyp as [[Hyp1 Hyp2] | [Hyp1 Hyp2]] ; apply (@f_equal (list A) _ (@length A)) in Hyp1;
  rewrite app_length in Hyp1; assert (length l3 = 0) as Hp by lia ;
  rewrite length_zero_iff_nil in Hp ; rewrite Hp in Hyp2 ; auto.
Qed.

Fixpoint splitAt {A : Type} (n : nat) (xs : list A) : (list A * list A) := 
match n, xs with
| 0, _  => (nil, xs)
| S n, nil => (nil, nil)
| S n, x::xs => match splitAt n xs with
               (ys, zs) => (x :: ys , zs)
               end
end.

(* Eval compute in (splitAt 5 [1;2;3;4]).
Eval compute in (splitAt 2 [1;2;3;4]). *)

Require Import FunInd.
Functional Scheme splitAt_ind := Induction for splitAt Sort Prop.

Lemma length_splitAt : forall A (l : list A) n l0 l1 , 
n <= length l -> splitAt n l = (l0, l1) ->
length l0 = n.
Proof.
intros A l n.
functional induction (splitAt n l) using splitAt_ind; simpl ; intros; inversion_clear H0; auto.
+ inversion H.
+ simpl. apply IHp in e1 ; auto. lia.   
Qed.

Lemma app_splitAt : forall A (l : list A) n l0 l1 , 
n <= length l -> splitAt n l = (l0, l1) ->
l = l0 ++ l1.
Proof.
intros A l n.
functional induction (splitAt n l) using splitAt_ind; simpl ; intros. 
+ inversion_clear H0; auto.
+ inversion H. 
+ apply le_S_n in H. inversion H0.
  rewrite (IHp ys zs H e1). rewrite H3; auto. 
Qed.

Lemma overflow_splitAt : forall A (l : list A) n, 
n > length l -> splitAt n l = (l, nil).
Proof.
intros A l n.
functional induction (splitAt n l) using splitAt_ind; simpl ; intros; auto. 
+ assert (0 <= length xs) by (auto with *) ;  lia.
+ assert (n0 > length xs0) as Hyp by lia .
  rewrite (IHp Hyp) in e1. inversion e1 ; auto.
Qed.



(*******************************************)

(* Binary numbers*)

Inductive Bin : Type :=
  |  epsilon  : Bin
  |  IB : Bin -> Bin
  |  OB : Bin -> Bin.

Local Notation "!" := epsilon.

Notation "p ~ 1" := (IB p)
 (at level 7, left associativity, format "p '~' '1'") : Bin_scope.
Notation "p ~ 0" := (OB p)
 (at level 7, left associativity, format "p '~' '0'") : Bin_scope.

Local Open Scope Bin_scope.


Fixpoint Bin2Nat_g (bs : Bin) (k : nat) : nat := 
  match bs with
  | ! => 0
  | bs ~ 0 =>  Bin2Nat_g bs (1 + k)
  | bs ~ 1 =>  2 ^ k + Bin2Nat_g bs (1 + k)
  end.

Definition Bin2Nat b := Bin2Nat_g b 0.

Eval compute in (!~ 1 ~ 0).
Eval compute in (Bin2Nat (OB (IB epsilon))).
Eval compute in (Bin2Nat !~ 1 ~ 0).
Eval compute in (Bin2Nat !~ 1 ~ 0 ~ 1).
Eval compute in (Bin2Nat !~ 0~ 1 ~ 0 ~ 1).

(* QC *)
From QuickChick Require Import QuickChick Tactics.

Module DoNotation.
Notation "'do!' X <- A ; B" :=
  (bindGen A (fun X => B))
    (at level 200, X ident, A at level 100, B at level 200).
End DoNotation.

Import DoNotation.

Derive (Arbitrary, Show) for Bin.

Derive (Show) for list.
(* Showlist is defined*)

Fixpoint genlist_lenght {A : Type} {mu0_ : Gen A} (size :nat) :=
match size with
 | 0 => returnGen []
 | S size' => do! p0 <- arbitrary;
              do! p1 <- genlist_lenght size';
              returnGen (p0 :: p1)
end.

(* list of natural numbers generator *)
Definition gen_listnat n : G (list nat) := genlist_lenght n.

Sample (gen_listnat 3).

(* Bin generator *)
Definition gen_Bin n : G Bin := 
@arbitrarySized _ GenSizedBin n.

Sample (gen_Bin 5).
(* [epsilon; IB (OB (OB (IB (IB epsilon))));
 OB (OB (OB (OB (IB epsilon)))); 
OB (IB (IB (IB (OB epsilon)))); 
IB (OB epsilon); IB epsilon; epsilon; 
OB (IB epsilon); IB (IB (OB (IB epsilon))); 
OB (IB (OB (IB (OB epsilon)))); IB epsilon]
*)



Module Type Container.
(* T is the type of the container *)
(* required interface for T *)
Parameter T : Type -> Type.
Parameter T_size : forall {A}, T A -> nat.
Parameter T_toList : forall {A}, T A -> list A.
Parameter T_toList_length : forall A (t : T A),  List.length (T_toList t)  = T_size t.
Parameter T_fromList : forall {A}, list A -> (T A).
Parameter T_fromList_size : forall A (l : list A), T_size (T_fromList l)  = List.length l.	   
Parameter T_toList_T_fromList : forall A (l : list A), T_toList (T_fromList l) = l.
Parameter T_fromList_T_toList : forall A (t : T A), T_fromList (T_toList t) = t.
End Container.

(* T decorated binary numbers *)
(*                            *)
Module DBin_T (Import container : Container).
Inductive DBin (A : Type) : Type :=
| Eps :  DBin A
| ZeroD : DBin A -> DBin A
| OneD :  DBin A -> T A -> DBin A.
Arguments Eps {A}.
Arguments ZeroD {A} d.
Arguments OneD {A} d t.


(* well-formed T decorated binary numbers*)

(* ZeroD waits for no data - OneD  waits for p data *)
Inductive inv {A : Type} : nat -> DBin A -> Prop :=
| inv_eps : forall p, inv p Eps
| inv_zero : forall p bs,
      inv (1+p) bs -> inv p (ZeroD bs)
| inv_one : forall p t bs,
      inv (1+p) bs -> T_size t = 2^p -> 
      inv p (OneD bs t)
.


Definition wfDBin {A : Type} := @inv A 0.

(* translation of a DBin to a Bin: erasure of data *)
Fixpoint forget {A : Type} (t : DBin A) : Bin :=
match t with
| Eps => epsilon
| ZeroD bs => OB (forget bs) 
| OneD bs t => IB (forget bs)
end.

(* translation of a DBin to the list of data contained in the former *)
Fixpoint DBintoList {A : Type} (t : DBin A) : list A :=
match t with
| Eps => nil
| ZeroD bs =>  DBintoList bs
| OneD bs t => T_toList t ++ DBintoList bs
end.

Lemma length_forget_g : forall (A : Type) (t : DBin A) k, 
inv k t -> List.length (DBintoList t) = Bin2Nat_g (forget t) k.
Proof.
induction t; simpl; intros; inversion_clear H; auto.
rewrite app_length.
rewrite T_toList_length. auto.
Qed.

Lemma length_forget : forall (A : Type) (t : DBin A), 
wfDBin t -> List.length (DBintoList t) = Bin2Nat (forget t).
Proof.
unfold wfDBin, Bin2Nat.
intros. apply length_forget_g ; assumption.	  
Qed.

(* From a list of data and a Bin (structure), build a DBin *)
Fixpoint fromBinList_g {A : Type} (b : Bin) (l : list A) (k : nat) : DBin A :=
match b with
| ! => Eps
| bs ~ 0 => ZeroD (fromBinList_g bs l (1+k))
| bs ~ 1 => match splitAt (2^k) l with
               (t, xs) => OneD (fromBinList_g bs xs (1+k)) (T_fromList t)
               end
end.

(* build a DBin from a Bin and a list of data *)
Definition fromBinList {A : Type} b l := @fromBinList_g A b l 0.

Lemma inv_fromBinList_g : forall (A : Type) b (xs : list A) k, 
List.length xs = Bin2Nat_g b k -> inv k (fromBinList_g b xs k).
Proof.
induction b ; simpl; intros; try constructor; auto.
case_eq xs; intros. 
+ subst. simpl in H. 
  assert (0 < 2 ^ k ) as Hyp.
    apply Nat.le_lt_trans with (m := k). lia. apply (Nat.pow_gt_lin_r 2 k);lia.
  lia.
+ subst ; simpl in H.
  case_eq (splitAt (2 ^ k) (a :: l)); intros. 
  assert (2 ^ k  <= List.length (a :: l)) as Hyp by (simpl;lia).
  pose proof (app_splitAt _ (a::l) (2 ^ k ) l0 l1 Hyp H0) as Hyp1.
  pose proof (length_splitAt _ (a::l) (2 ^ k) l0 l1 Hyp H0) as Hyp2.
  apply (@f_equal (list A) _ (@List.length A)) in Hyp1. rewrite app_length in Hyp1. simpl in Hyp1. 
  rewrite Hyp2 in Hyp1; rewrite H in Hyp1. 
  constructor.
  apply IHb. lia.
  rewrite T_fromList_size ; assumption.
Qed.

Lemma wf_fromBinList : forall (A : Type) b (xs : list A), 
List.length xs = Bin2Nat b -> wfDBin (fromBinList b xs).
Proof.
unfold wfDBin, Bin2Nat.
intros. apply inv_fromBinList_g ; assumption.
Qed.	 

(* cancellation lemmas*)
Lemma DBintoList_fromBinList_g : forall (A : Type) b (xs : list A) k, 
List.length xs = Bin2Nat_g b k ->  DBintoList (fromBinList_g b xs k) = xs.
Proof.
induction b ; simpl; intros.
+ apply length_zero_iff_nil in H ; auto.
+ case_eq (splitAt (2 ^ k) xs) ; intros. simpl.
assert (2 ^ k  <= List.length xs) as Hyp by (simpl;lia).
pose proof (app_splitAt _ xs (2 ^ k ) l l0 Hyp H0).
rewrite IHb. rewrite T_toList_T_fromList. auto.
pose proof (length_splitAt _ xs (2 ^ k) l l0 Hyp H0).
apply (@f_equal (list A) _ (@List.length A)) in H1. 
rewrite app_length in H1. lia.
+ apply  IHb ; auto.
Qed.


Lemma DBintoList_fromBinList : forall (A : Type) b (xs : list A), 
List.length xs = Bin2Nat b ->  DBintoList (fromBinList b xs) = xs.
Proof.
unfold DBintoList, fromBinList, Bin2Nat.
intros. apply DBintoList_fromBinList_g ; assumption.
Qed.


Lemma fromBinList_DBintoList : forall (A : Type) (t : DBin A) k, 
inv k t -> fromBinList_g (forget t) (DBintoList t) k  = t.
Proof.
induction t ; simpl ; intros ; auto.
+ inversion_clear H. rewrite IHt ; auto.
+ case_eq (splitAt (2 ^ k) (T_toList t0 ++ DBintoList t)) ; intros. 
  inversion_clear H. rewrite <-  T_toList_length in H2.
  assert (2 ^ k <= List.length (T_toList t0 ++ DBintoList t)) as Hle by 
    (rewrite app_length; lia).  
   pose proof (app_splitAt _ _ _ _ _ Hle H0) as Hyp1.
   pose proof (length_splitAt _ _ _ _ _ Hle H0) as Hyp2.
   assert (List.length (T_toList t0) = List.length l) as Hyp3 by lia.   
   pose proof (app_eq_app_helper2 _ _ _ _ _ Hyp1 Hyp3) as Hyp4.
   assert (T_toList t0 = l) as Hyp5 by 
     (rewrite <- Hyp4 in Hyp1; apply app_eq_app_helper3 in Hyp1 ; auto).
   rewrite <- Hyp4. rewrite IHt; auto.
   rewrite <- Hyp5.
   rewrite T_fromList_T_toList ; reflexivity.
Qed.

Lemma fromList_toList : forall (A : Type) (t : DBin A) , 
wfDBin t -> fromBinList (forget t) (DBintoList t)   = t.
Proof.
unfold wfDBin, fromBinList, DBintoList.
intros. apply fromBinList_DBintoList ; auto.
Qed.


Open Scope string.


Fixpoint DBin_print { A : Type} `{sh : Show (T A)} ( t : DBin A):=
  match t with
     Eps => "!"
    |ZeroD d  => @DBin_print A sh d ++ "0"
    | OneD d t => (@DBin_print A sh d) ++ "(" ++ show t ++ ")" ++ "1"
  end.


Fixpoint invb {A : Type} (p : nat) (t : DBin A)  :=
match t with
  Eps => true
| ZeroD bs => invb (S p) bs
| OneD bs t =>  andb (Nat.eqb (T_size t) (2^p))  (invb (S p) bs)
end.

Definition wfDBinb {A : Type} := @invb A 0.

(** TODO prove correctness of invb wrt inv**)
(* Try QC facility or derive command from sniper pluggin
 *)




Fixpoint DBin_gen_sized ( A : Type) (size : nat) : G (DBin nat):=
match size with
| 0 => returnGen (Eps)
| S size' => 
             do! b <- gen_Bin size';
             do! l <- genlist_lenght (Bin2Nat b);
             returnGen (fromBinList b l)
 end.
 
End DBin_T.

Module List_Container : Container.
Definition T := list.
Definition T_size := List.length.
Definition T_toList :=  fun {A :Type} (l : list A) => l. 
Lemma T_toList_length : forall A (t : T A),  List.length (@T_toList _ t)  = T_size _ t.
Proof. auto. Qed.
Definition T_fromList := fun {A :Type} (l : list A) => l.
Lemma T_fromList_size : forall A (l : list A), T_size _ (@T_fromList _ l)  = List.length l .	   
Proof. auto. Qed.
Lemma T_toList_T_fromList : forall A (l : list A), T_toList (T_fromList l) = l.
Proof. auto. Qed.
Lemma T_fromList_T_toList : forall A (t : T A), T_fromList (T_toList t) = t.
Proof. auto. Qed.
End List_Container.

Module DBin_list := DBin_T (List_Container).

(**
Sample (DBin_list.DBin_gen_sized nat 3).
(*QuickChecking (DBin_list.DBin_gen_sized nat 3)
Unable to satisfy the following constraints:

?Show : "Show
           (list
              (DBin_list.DBin
                 nat))"*)
**)

(** QuickCheck (sized (fun n => 
  forAll (DBin_list.DBin_gen_sized nat n) (fun t => 
   DBin_list.wfDBinb t))).
(* QuickChecking (sized
   (fun n =>
    forAll (DBin_list.DBin_gen_sized nat n) (fun t => DBin_list.wfDBinb t)))
Unable to satisfy the following constraints:
In environment:
n : nat

?H : "Show
        (DBin_list.DBin nat)"*)
 
 **)

