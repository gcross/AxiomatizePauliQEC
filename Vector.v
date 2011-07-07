Require Import Arith Le Tactics JMeq.

Infix "==" := JMeq (at level 70, no associativity).

Section Vectors.
  Variable A : Type.

  Inductive vector : nat -> Type :=
  | nil : vector 0
  | cons : forall {n:nat} (a:A), vector n -> vector (S n).

  Infix "::" := cons (at level 60, right associativity) : vector_scope.
  Open Scope vector_scope.

  Lemma equal_means_equal_cons : forall {n:nat} (a b:A) (v:vector n) (w:vector n), a :: v = b :: w <-> (a = b /\ v = w).
    crush;  injection H;  crush.
  Qed.

  Lemma two_cases_of_vector_values {n:nat} (v:vector n) : {x:A & {m:nat & {xs:vector m | v == x::xs /\ n = S m}}} + {v==nil /\ n = 0}.
    intros.  induction v as [|m x xs].
    right.  crush.
    left.  exists x.  exists m.  exists xs.  crush.
  Qed.

  Definition deconstruct_vector {n:nat} (v:vector (S n)) : {t:(A*vector n) | let (x,xs) := t in x::xs = v}.
    intros.  set (two_cases_of_vector_values v).  crush.
    inversion a. crush. inversion X.  crush. inversion X0.  assert (n = x0).  crush.  crush.  exists (x,x1).  reflexivity.
  Qed.

  Definition head {n:nat} (v:vector (S n)) : A :=
    match v with
      | cons _ x _ => x
      | _ => False
    end.

  Lemma head_returns_prepended_element : forall {n:nat} {a:A} {v:vector n}, head (a :: v) = a.
    auto.
  Qed.

  Definition tail {n:nat} (v:vector (S n)) : vector n :=
    match v with
      | cons _ _ xs => xs
      | _ => False
    end.

  Lemma tail_returns_appended_vector : forall {n:nat} {a:A} {v:vector n}, tail (a :: v) = v.
    auto.
  Qed.

  Lemma nonempty_vector_equals_head_cons_tail : forall {n:nat} (v:vector (S n)), v = head v :: tail v.
    intros.  induction n.  

  Definition nthElementOf {m:nat} (n:nat) {pf: m < n} (v:vector n) : A.
    induction m as [|m f].
    intros n v.  inversion v as [|n0 x xs].  exact x.
    

  Definition last {n:nat} (v:vector (S n)) : A.
  induction n as [| n f]. intros v.  inversion v.  exact a.
  intros v.  inversion v.  exact (f X).
  Defined.

  Lemma cons_leaves_last_constant : forall {n:nat} {a:A} {v:vector (S n)}, last v = last (a :: v).
    auto.
  Qed.

  Fixpoint const (a:A) (n:nat) :=
    match n return vector n with
      | O => nil
      | S n => a :: (const a n)
    end.

  Definition length {n:nat} (_:vector n) : nat := n.

  Lemma length_is_correct : forall {n:nat} {v:vector n}, length v = n.
    auto.
  Qed.

  Fixpoint append {m:nat} {n:nat} (v:vector m) (w:vector n) : vector (m+n) :=
    match v with
      | nil => w
      | cons _ x xs => x :: (append xs w)
    end.

  Infix "++" := append (right associativity, at level 60) : vector_scope.

  Definition singleton (a:A) : vector 1 := a :: nil.

  Definition reverse {n:nat} (v:vector n) : vector n.
    induction n as [| n f].  auto.
    intro v.  inversion v as [|n' x xs].  clear v H0 n'.
      set (reversed_v := f xs ++ singleton x). assert (n + 1 = S n).  crush.  crush.
  Defined.

  Definition toList {n:nat} (v:vector n) : list A.
    induction n as [|n f].  intros.  exact (List.nil : list A).
    intros.  inversion v as [|n0 x xs].  exact (List.cons x (f xs)).
  Defined.

  Definition id {n:nat} : vector n -> vector n :=
    match n with
    | 0 => fun _ => nil
    | _ => fun v => head v :: tail v
    end.

  Lemma id_produces_equal_vector : forall {n:nat} (v:vector n), v = id v.
    destruct v; auto.
  Defined.

  Lemma non_empty_vector_is_cons : forall {n:nat} (v:vector (S n)), v = head v :: tail v.
    intros.  exact (id_produces_equal_vector v).
  Qed.

  Lemma empty_vector_is_nil : forall (v:vector 0), v = nil.
    intros.  exact (id_produces_equal_vector v).
  Qed.

  Lemma equal_size_implies_equal_types : forall {n m:nat}, m = n -> vector m = vector n.
    crush.
  Qed.

  Lemma appending_nil_to_nil_obtains_nil : nil ++ nil = nil.
    crush.
  Qed.

  Lemma prepending_nil_is_identity : forall {n:nat} (v:vector n), nil ++ v = v.
    crush.
  Qed.

  Lemma prepending_equal_vectors_obtains_same_result : forall {m n:nat} (v1:vector m) (v2:vector m) (w:vector n), v1 = v2 -> v1 ++ w = v2 ++ w.
    crush.
  Qed.

  Lemma prepending_element_is_associative_with_append : forall {m n:nat} (a:A) (v:vector m) (w:vector n), (a :: v) ++ w = a :: (v ++ w).
    crush.
  Qed.

  Lemma equal_implies_equal_cons_with_nil : forall (a b:A), a = b -> a :: nil = b :: nil.
    crush.
  Qed.

  Lemma unequal_cons_with_nil_means_unequal : forall (a b:A),  a :: nil <> b :: nil -> a <> b.
    crush.
  Qed.

  Lemma unequal_implies_unequal_cons_with_nil :
    forall (a b:A),
      a <> b -> a :: nil <> b :: nil.
    crush.

  Lemma equal_means_equal_cons : forall {m n:nat} (a b:A) (v:vector n) (w:vector n), a :: v = b :: w <-> (a = b /\ v = w).
    intros.
    induction n.  rewrite(empty_vector_is_nil v). rewrite(empty_vector_is_nil w).  crush.


  Lemma appending_nil_is_identity : forall {n:nat} (v:vector n), v ++ nil == v.
    induction n as [|n f]; crush.  rewrite empty_vector_is_nil.  rewrite (prepending_equal_vectors_obtains_same_result nil (empty_vector_is_nil v)).  crush.
    rewrite(non_empty_vector_is_cons v).  rewrite(prepending_element_is_associative_with_append).
  Qed.


rewrite(empty_vector_is_nil v).  rewrite(empty_vector_is_nil w).  reflexivity.
    rewrite(non_empty_vector_is_cons v).  rewrite(non_empty_vector_is_cons w).


  Lemma append_is_associative : forall {l m n:nat} (u: vector l) (v: vector m) (w: vector n), (u ++ v) ++ w == (u ++ (v ++ w)).
    induction l; crush.