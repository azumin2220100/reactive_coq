(* ライブラリのImport *)
From Coq 
  Require Import Streams.
From mathcomp
  Require Import ssrnat.

Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).
Notation "x ⊕ y" := (app x y)
                     (at level 75, right associativity).


Section reactive.

Variables I O I_cup_O: Type.
Variable ε : I.


(* 有限列と無限列の結合 *)
Fixpoint list_plus_Stream
  (U : Type) (l1 : list U) (l2 : Stream U) : Stream U :=
  match l1 with
    | cons hd tl =>
      Cons hd (list_plus_Stream U tl l2)
    | nil =>
      l2
  end.

Arguments list_plus_Stream {U} _ _.
Notation "x @ y" := (list_plus_Stream x y)
                     (at level 78, no associativity).


(* 定義１　リアクティブシステム　*)
Definition R 
  := (list I) -> O.


(* 定義２　無限列に対するリアクティブシステムの出力 *)
CoFixpoint R_omega'
    (r : R)
    (pref : list I)
    (l : Stream I) : Stream O :=
  match l with
  | Cons hd tl =>
      let new_pref := pref ⊕ [hd] in
      Cons (r [hd]) (R_omega' r new_pref tl)
  end.

Definition R_omega 
    (r : R)
    (l : Stream I): Stream O :=
  R_omega' r nil l.


(* 定義２'　有限列に対するリアクティブシステムの出力 *)
Fixpoint R_omega_fin'
    (r : R)
    (pref : list I)
    (l : list I) : list O :=
  match l with
  | cons hd tl =>
      let new_pref := pref ⊕ [hd] in
      cons (r [hd]) (R_omega_fin' r new_pref tl)
  | nil =>
      nil
  end.

Definition R_omega_fin
    (r : R)
    (l : list I) : list O :=
  R_omega_fin' r nil l.


(* <α,β> の定義 *)
Variable cup
  : I -> O -> I_cup_O.

Notation "x ∪ y" := (cup x y)
                    (at level 55, right associativity).

CoFixpoint stepwise_union
  (l1 : Stream I)(l2 : Stream O) : Stream I_cup_O :=
  match l1 with
    | Cons hd1 tl1 =>
      match l2 with
        | Cons hd2 tl2 =>
          Cons (hd1 ∪ hd2) (stepwise_union tl1 tl2)
      end
  end.

Notation " 〈 x , y 〉 " := (stepwise_union x y)
                      (at level 65, right associativity).


(* 定義３　リアクティブシステムの振る舞い　*)
Definition behavior
  (r : R) (l : Stream I) :=
  〈 l, (R_omega r l) 〉: Stream I_cup_O.


(* 定義４　リアクティブシステム仕様　*)
Variable S' :
  Stream I_cup_O -> Prop.

Definition In_S {U} (S : U -> Prop) (x : U) : Prop := S x.

Notation " x ∈ S' " := (In_S S' x)
                      (at level 60, no associativity).


(* 階層定理の証明に用いる定義 *)
CoFixpoint empty_list : Stream I :=
  Cons ε empty_list.

Fixpoint empty_list_fin (m : nat) : list I :=
  match m with
    | S n => ε :: (empty_list_fin n)
    | 0 => nil
  end.


(* 階層定理の証明に用いる定理 *)
Lemma empty_list_fin_length :
  forall m : nat,
    length (empty_list_fin m) = m.
Proof.
  intro m.
  induction m as [ | m IHm ].
    - simpl. reflexivity.
    - simpl. rewrite -> IHm. reflexivity.
Qed. 

Lemma R_omega_fin'_eq_length :
  forall a_bar pref : list I, forall r : R,
    length (R_omega_fin' r pref a_bar) = length a_bar.
Proof.
  induction a_bar as [ | hd tl IHa_bar].
    + intro pref.
      intro r.
      simpl. reflexivity.
    + intro pref.
      intro r.
      simpl.
      specialize(IHa_bar (pref ⊕ [hd])).
      specialize(IHa_bar r).
      rewrite -> IHa_bar. reflexivity.
Qed.


(* 階層定理の証明に用いる仮定 *)
Hypothesis divide_colist :
  forall U : Type,
    forall l : Stream U,
      forall m : nat,
        exists l_bar : list U,
          exists l_hat : Stream U,
            (l = (l_bar @ l_hat)) /\ (length l_bar = m).

Hypothesis R_omega_fin_to_R_omega :
  forall a_bar : list I,
    forall a_hat : Stream I,
      forall r : R,
        R_omega r (a_bar @ a_hat) =
         ((R_omega_fin r a_bar) @ (R_omega' r a_bar a_hat)).


(* 定義５ 実現可能性 *)
Definition Real : Prop :=
  exists r : R,
    forall a : Stream I,
       〈a, (R_omega r a)〉 ∈ S'.


(* 定義６～定義１７　実現可能性の必要条件 *)
Definition Sat : Prop :=
  exists a : Stream I,
    exists b : Stream O,
      〈a, b〉∈ S' . 

Definition StrSat : Prop :=
  forall a : Stream I,
    exists b : Stream O,
      〈a, b〉∈ S'.

Definition PresSat : Prop :=
  exists r : R,
    forall a_bar : list I,
      exists a_hat : Stream I,
        exists b_hat : Stream O,
          〈(a_bar @ a_hat), ((R_omega_fin r a_bar) @ b_hat)〉∈ S'.

Definition PresStrSat : Prop :=
  exists r : R,
    forall a_bar : list I,
      forall a_hat : Stream I,
        exists b_hat : Stream O,
          〈(a_bar @ a_hat), ((R_omega_fin r a_bar) @ b_hat)〉∈ S'.

Definition PrefSat : Prop :=
  forall a_bar : list I,
    exists a_hat : Stream I,
      exists b_bar : list O,
        (length b_bar = length a_bar /\
          (exists b_hat : Stream O,
            〈a_bar @ a_hat, b_bar @ b_hat〉∈ S')).

Definition SuffSat : Prop :=
  forall a_hat : Stream I,
    exists a_bar : list I,
      exists b : Stream O,
        〈a_bar @ a_hat, b〉 ∈ S'.

Definition PropSuffSat : Prop :=
  exists a_bar : list I,
    exists b_bar : list O,
      (length b_bar = length a_bar /\
        forall a_hat : Stream I,
          exists b_hat : Stream O,
            〈a_bar @ a_hat, b_bar @ b_hat〉∈ S' ).

Definition PropStrSat : Prop :=
  forall a_bar : list I,
    exists b_bar : list O,
      (length b_bar = length a_bar /\
        forall a_hat : Stream I,
          exists b_hat : Stream O,
            〈a_bar @ a_hat, b_bar @ b_hat〉∈ S').

Definition PropPresSat : Prop :=
  exists r : R,
    forall a_bar : list I,
      exists a_hat : Stream I,
       〈a_bar @ a_hat, (R_omega r (a_bar @ a_hat))〉∈ S'.

Definition StabSat : Prop :=
  exists r : R,
    forall a_hat : Stream I,
      exists a_bar : list I,
        exists b_bar : list O,
          (length b_bar = length a_bar /\
            〈a_bar @ a_hat, b_bar @ (R_omega r a_hat)〉∈ S' ).

Definition PropStabSat : Prop :=
  exists r : R,
    exists a_bar : list I,
      exists b_bar : list O,
        (length b_bar = length a_bar /\
          (forall a_hat : Stream I,
            〈a_bar @ a_hat, b_bar @ (R_omega r a_hat)〉∈ S' )).

Definition StabStrSat : Prop :=
  exists n : nat,
    forall m : nat, 
      forall a_bar : list I,
        (((le n m) /\ (length a_bar = m)) ->
          (exists b_bar : list O,
            (length b_bar = m /\
              (exists r : R,
                forall a_hat : Stream I,
                  〈a_bar @ a_hat , b_bar @ (R_omega r a_hat)〉∈ S' )))).



(* 階層定理の証明1  Real -> StabStrSat -> PropStabSat 
                      -> PropSuffSat -> SuffSat -> Sat *)

Theorem Real_to_StabStrSat :
  Real -> StabStrSat.
Abort.

Theorem StabStrSat_to_PropStabSat :
  StabStrSat -> PropStabSat.
Proof.
  unfold StabStrSat, PropStabSat.
  intro H.
  destruct H as [n H].
  specialize(H n).
  specialize(H (empty_list_fin n)).
  pose proof(le_n n) as H2.
  pose proof(empty_list_fin_length n) as H3.
  specialize (H (conj H2 H3)).
  destruct H as [b_bar H].
  destruct H as [H4 H5].
  destruct H5 as [r H5].
  exists r. exists (empty_list_fin n). exists b_bar.
  split.
    + rewrite H3. trivial.
    + intro a_hat.
      specialize(H5 a_hat). trivial.
Qed.

Theorem PropStabSat_to_PropSuffSat :
  PropStabSat -> PropSuffSat.
Proof.
  unfold PropStabSat, PropSuffSat.
  intro H.
  destruct H as [r H].
  destruct H as [a_bar H].
  destruct H as [b_bar H].
  destruct H as [H2 H3].
  exists a_bar. exists b_bar.
  split.
    + trivial.
    + intro a_hat.
      specialize(H3 a_hat).
      exists (R_omega r a_hat). trivial.
Qed.

Theorem PropSuffSat_to_SuffSat :
  PropSuffSat -> SuffSat.
Proof.
  unfold PropSuffSat, SuffSat.
  intro H.
  intro a_hat.
  destruct H as [a_bar H].
  destruct H as [b_bar H].
  destruct H as [H2 H3].
  specialize(H3 a_hat).
  destruct H3 as [b_hat H3].
  exists a_bar. exists (b_bar @ b_hat). trivial.
Qed.

Theorem SuffSat_to_Sat :
  SuffSat -> Sat.
Proof.
  unfold SuffSat, Sat.
  intro H.
  specialize(H empty_list).
  destruct H as [a_bar H].
  destruct H as [b H].
  exists (a_bar @ empty_list).
  exists b. trivial.
Qed.


(* 階層定理の証明2  Real -> PresStrSat -> PropStrSat 
                      -> StrSat -> PropSuffSat *)
Theorem Real_to_PresStrSat :
  Real -> PresStrSat.
Proof.
  unfold Real, PresStrSat.
  intro H.
  destruct H as [r H].
  exists r.
  intro a_bar.
  intro a_hat.
  specialize(H (a_bar @ a_hat)).
  pose proof (R_omega_fin_to_R_omega a_bar a_hat r).
  rewrite -> H0 in H.
  exists (R_omega' r a_bar a_hat). trivial.
Qed.

Theorem PresStrSat_to_PropStrSat :
  PresStrSat -> PropStrSat.
Proof.
  unfold PresStrSat, PropStrSat.
  intro H.
  intro a_bar.
  destruct H as [r H].
  specialize(H a_bar).
  exists (R_omega_fin r a_bar).
  split.
    + pose proof (R_omega_fin'_eq_length a_bar nil r).
      trivial.
    + intro a_hat.
      specialize(H a_hat).
      destruct H as [b_hat H].
      exists b_hat. trivial.
Qed.

Theorem PropStrSat_to_StrSat :
  PropStrSat -> StrSat.
Proof.
  unfold PropStrSat, StrSat.
  intro H.
  intro a.
  specialize(H nil).
  destruct H as [b_bar H].
  destruct H as [H2 H3].
  specialize(H3 a).
  destruct H3 as [b_hat H3].
  simpl in H3.
  exists (b_bar @ b_hat). trivial.
Qed.

Theorem StrSat_to_PropSuffSat :
  StrSat -> PropSuffSat.
Proof.
  unfold StrSat, PropSuffSat.
  intro H.
  do 2 exists nil.
  split.
    + reflexivity.
    + intro a_hat.
      specialize(H a_hat).
      destruct H as [b H].
      exists b.
      simpl. trivial.
Qed.


(* 階層定理の証明3  Real -> PropPresSat -> PresSat 
                      -> PrefSat -> Sat *)
Theorem Real_to_PropPresSat :
  Real -> PropPresSat.
Proof.
  unfold Real, PropPresSat.
  intro H.
  destruct H as [r H].
  exists r.
  intro a_bar.
  exists empty_list.
  specialize(H (a_bar @ empty_list)). trivial.
Qed.

Theorem PropPresSat_to_PresSat :
  PropPresSat -> PresSat.
Proof.
  unfold PropPresSat, PresSat.
  intro H.
  destruct H as [r H].
  exists r.
  intro a_bar.
  specialize(H a_bar).
  destruct H as [a_hat H].
  exists a_hat.
  pose proof (R_omega_fin_to_R_omega a_bar a_hat r).
  rewrite H0 in H.
  exists (R_omega' r a_bar a_hat). trivial.
Qed.

Theorem PresSat_to_PrefSat :
  PresSat -> PrefSat.
Proof.
  unfold PresSat, PrefSat.
  intro H.
  intro a_bar.
  destruct H as [r H].
  specialize(H a_bar).
  destruct H as [a_hat H].
  destruct H as [b_hat H].
  exists a_hat.
  exists (R_omega_fin r a_bar).
  split.
    + induction a_bar as [ | hd tl IHa_bar].
        - simpl. reflexivity.
        - simpl. 
          pose proof (R_omega_fin'_eq_length tl [hd] r).
          rewrite H0. reflexivity.
    + exists b_hat. trivial.
Qed.

Theorem PrefSat_to_Sat :
  PrefSat -> Sat.
Proof.
  unfold PrefSat, Sat.
  intro H.
  specialize(H nil).
  destruct H as [a_hat H].
  destruct H as [b_bar H].
  destruct H as [H2 H3].
  destruct H3 as [b_hat H3].
  exists(nil @ a_hat).
  exists(b_bar @ b_hat). trivial.
Qed.

(* 階層定理の証明4  PropStabSat -> StabSat -> SuffSat *)
Theorem PropStabSat_to_StabSat :
  PropStabSat -> StabSat.
Proof.
  unfold PropStabSat, StabSat.
  intro H.
  destruct H as [r H].
  destruct H as [a_bar H].
  destruct H as [b_bar H].
  destruct H as [H2 H3].
  exists r.
  intro a_hat.
  specialize (H3 a_hat).
  exists a_bar.
  exists b_bar.
  split.
    + trivial.
    + trivial.
Qed.

Theorem StabSat_to_SuffSat :
  StabSat -> SuffSat.
Proof.
  unfold StabSat, SuffSat.
  intro H.
  intro a_hat.
  destruct H as [r H].
  specialize(H a_hat).
  destruct H as [a_bar H].
  destruct H as [b_bar H].
  destruct H as [H2 H3].
  exists a_bar.
  exists (b_bar @ R_omega r a_hat). trivial.
Qed.


(* 階層定理の証明5  StabStrSat -> StrSat -> PrefSat *)
Theorem StabStrSat_to_StrSat :
  StabStrSat -> StrSat.
Proof.
  unfold StabStrSat, StrSat.
  intro H.
  destruct H as [n H].
  specialize(H n).
  intro a.
  pose proof (divide_colist I a n) as H2.
  destruct H2 as [a_bar H2].
  destruct H2 as [a_hat H2].
  destruct H2 as [H3 H4].
  specialize(H a_bar).
  pose proof(le_n n) as H5.
  specialize (H (conj H5 H4)).
  destruct H as [b_bar H].
  destruct H as [H6 H7].
  destruct H7 as [r H7]. 
  specialize(H7 a_hat).
  exists(b_bar @ R_omega r a_hat). 
  rewrite H3. trivial.
Qed.

Theorem StrSat_to_PrefSat :
  StrSat -> PrefSat.
Proof.
  unfold StrSat, PrefSat.
  intro H.
  intro a_bar.
  specialize(H (a_bar @ empty_list)).
  destruct H as [b H].
  pose proof (divide_colist O b (length a_bar)) as H2.
  destruct H2 as [b_bar H2].
  destruct H2 as [b_hat H2].
  destruct H2 as [H3 H4].
  exists empty_list.
  exists b_bar.
  split.
    - trivial.
    - exists b_hat. 
      rewrite <- H3. trivial.
Qed.


(* 階層定理の証明6  PresStrSat -> PresSat *)
Theorem PresStrSat_to_PresSat :
  PresStrSat -> PresSat.
Proof.
  unfold PresStrSat, PresSat.
  intro H.
  destruct H as [r H].
  exists r.
  intro a_bar.
  specialize(H a_bar).
  specialize(H empty_list).
  destruct H as [b_hat H].
  exists empty_list.
  exists b_hat.
  trivial.
Qed.