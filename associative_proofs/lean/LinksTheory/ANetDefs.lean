import Init.Data

-- Последовательность идентификаторов векторов: L ⊆ ℕ₀
def L := Nat

-- Дефолтное значение L: ноль
def LDefault := 0

-- Множество векторов идентификаторов длины n ∈ ℕ₀: Vn ⊆ Lⁿ
def Vn (n : Nat) := Vec L n

-- Дефолтное значение Vn
def VnDefault (n : nat) : Vn n := vector.repeat LDefault n

-- Множество всех ассоциаций: A = L × Vn
def A (n : nat) := prod L (Vn n)

-- Ассоциативная сеть векторов длины n (или n-мерная асеть) из семейства функций {anetvⁿ : L → Vn}
def ANetVf (n : nat) := L → Vn n
def ANetVl (n : nat) := list (Vn n)

-- Вложенные упорядоченные пары
def NP := list L

notation `[]` := list.nil
notation `[` x `, .. ,` y `]` := list.cons x .. (list.cons y list.nil) ..

-- Ассоциативная сеть вложенных упорядоченных пар: anetl : L → NP
def ANetLf := L → NP
def ANetLl := list NP

-- Дуплет
def D := prod L L

-- Дефолтное значение D: пара из двух LDefault
def DDefault : D := (LDefault, LDefault)

-- Ассоциативная сеть дуплетов (или двумерная асеть): anetd : L → L²
def ANetDf := L → D
def ANetDl := list D
