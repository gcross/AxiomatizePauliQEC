Inductive Pauli : Set :=
| I
| X
| Y
| Z.

Definition product (a b : Pauli) : Pauli :=
  match (a,b) with
    | (I,_) => b
    | (_,I) => a
    | (X,X) => I
    | (Y,Y) => I
    | (Z,Z) => I
    | (X,Y) => Z
    | (Y,X) => Z
    | (Y,Z) => X
    | (Z,Y) => X
    | (Z,X) => Y
    | (X,Z) => Y
  end.

Lemma pauli_product_is_associative : forall (a b c: Pauli), product a (product b c) = product (product a b) c.
intros.  case a; case b; case c; auto.
Qed.
