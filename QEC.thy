theory QEC
imports Main
begin
datatype pauli =
    I
  | X
  | Y
  | Z

definition
  weightOfPauli :: "pauli => nat" where
  "weightOfPauli x =
    (case x of
       I => 0
     | _ => 1
    )"

types pauli_operator = "pauli list"

definition
  weightOfPauliOperator :: "pauli_operator => nat" where
  "weightOfPauliOperator xs = listsum (map weightOfPauli xs)"

primrec
  plusPauli :: "pauli => pauli => pauli" where
  "plusPauli I a = a" |
  "plusPauli X a =
      (case a of
         I => X
      |  X => I
      |  Y => Z
      |  Z => Y)
  " |
  "plusPauli Y a =
      (case a of
         I => Y
      |  X => Z
      |  Y => I
      |  Z => X)
  " |
  "plusPauli Z a =
      (case a of
         I => Z
      |  X => Y
      |  Y => X
      |  Z => I)
  "

lemma "plusPauli I x = x"
apply(case_tac x)
apply(auto)
done

lemma "!! x y z. plusPauli x (plusPauli y z) = plusPauli (plusPauli x y) z"
proof

