import CopelandErdos

open CopelandErdos.Normality

#check copelandErdos_normal
#check tendsto_copelandErdos_patternFrequency
#print axioms copelandErdos_normal
#print axioms tendsto_copelandErdos_patternFrequency

example : NormalInBase 10 copelandErdos := copelandErdos_normal

example : Real.digits copelandErdos 10 = CopelandErdos.Digits.primeDigits 10 (by decide) :=
  digits_copelandErdos
