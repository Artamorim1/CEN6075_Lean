import Init.System.IO

inductive Item
| Cotton_Shirt
| Polyester_Shirt
| Jeans
| Sweatpants
| Tennis_Shoes
| Running_Shoes
| Hat

deriving Repr, BEq

instance : ToString Item :=
  ⟨fun
    | Item.Cotton_Shirt   => "Cotton Shirt"
    | Item.Polyester_Shirt => "Polyester Shirt"
    | Item.Jeans => "Jeans"
    | Item.Sweatpants => "Sweatpants"
    | Item.Tennis_Shoes => "Tennis Shoes"
    | Item.Running_Shoes => "Running Shoes"
    | Item.Hat => "Hat"⟩

-- Price
def price : Item → Nat
  | Item.Cotton_Shirt => 25
  | Item.Polyester_Shirt => 20
  | Item.Jeans => 50
  | Item.Sweatpants => 30
  | Item.Tennis_Shoes => 70
  | Item.Running_Shoes => 80
  | Item.Hat => 15

-- I defined the states as tuples, because it is what i am confortable with
def ShoppingCart := (Nat × Nat × Nat × Nat × Nat × Nat × Nat)
def Stock := (Nat × Nat × Nat × Nat × Nat × Nat × Nat)

-- These next two are auxiliary functions that associate each Nat in the states with an item
def getItem (t : ShoppingCart) (i : Item) : Nat :=
  match i, t with
  | Item.Cotton_Shirt, (q, _, _, _, _, _, _) => q
  | Item.Polyester_Shirt, (_, q, _, _, _, _, _) => q
  | Item.Jeans, (_, _, q, _, _, _, _) => q
  | Item.Sweatpants, (_, _, _, q, _, _, _) => q
  | Item.Tennis_Shoes, (_, _, _, _, q, _, _) => q
  | Item.Running_Shoes, (_, _, _, _, _, q, _) => q
  | Item.Hat, (_, _, _, _, _, _, q) => q

def setItem (t : ShoppingCart) (i : Item) (q : Nat) : ShoppingCart :=
  match i, t with
  | Item.Cotton_Shirt, (_, b, c, d, e, f, g) => (q, b, c, d, e, f, g)
  | Item.Polyester_Shirt, (a, _, c, d, e, f, g) => (a, q, c, d, e, f, g)
  | Item.Jeans, (a, b, _, d, e, f, g) => (a, b, q, d, e, f, g)
  | Item.Sweatpants, (a, b, c, _, e, f, g) => (a, b, c, q, e, f, g)
  | Item.Tennis_Shoes, (a, b, c, d, _, f, g) => (a, b, c, d, q, f, g)
  | Item.Running_Shoes, (a, b, c, d, e, _, g) => (a, b, c, d, e, q, g)
  | Item.Hat, (a, b, c, d, e, f, _) => (a, b, c, d, e, f, q)


-- So i like to divide my specifications into 2 parts:
-- A functional spec (more free form and can return diff outputs) -> which helps implementation.
-- And a operational semantics which always returns a state -> helps formal proofs.
def getCost (sc : ShoppingCart) : Nat :=
 let (q1, q2, q3, q4, q5, q6, q7) := sc
  let (p1, p2, p3, p4, p5, p6, p7) := (25, 20, 50, 30, 70, 80, 15)
  q1 * p1 +
  q2 * p2 +
  q3 * p3 +
  q4 * p4 +
  q5 * p5 +
  q6 * p6 +
  q7 * p7

/--
def addItem (sc : ShoppingCart) (s : Stock) (i : Item) : ShoppingCart :=
  let q := getItem sc i
  let stockQty := getItem s i
  if q + 1 ≤ stockQty then setItem sc i (q + 1) else sc

def deleteItem (sc : ShoppingCart) (i : Item) : ShoppingCart :=
  setItem sc i 0

def changeQuantity (sc : ShoppingCart) (s : Stock) (i : Item) (q : Nat) : ShoppingCart :=
  let stockQty := getItem s i
  if q ≤ stockQty then setItem sc i q else sc
--/

-- So this function can be used to specify check out the Command check out by using checkout(sc) = true or false as preconditions.
-- I just chose not to to make the semantics stand on their own.
def checkout (sc : ShoppingCart) (payment : Nat) (s : Stock) : Bool :=
  let totalCost := getCost sc
  let validStock := (getItem sc Item.Cotton_Shirt ≤ getItem s Item.Cotton_Shirt) ∧
                    (getItem sc Item.Polyester_Shirt ≤ getItem s Item.Polyester_Shirt) ∧
                    (getItem sc Item.Jeans ≤ getItem s Item.Jeans) ∧
                    (getItem sc Item.Sweatpants ≤ getItem s Item.Sweatpants) ∧
                    (getItem sc Item.Tennis_Shoes ≤ getItem s Item.Tennis_Shoes) ∧
                    (getItem sc Item.Running_Shoes ≤ getItem s Item.Running_Shoes) ∧
                    (getItem sc Item.Hat ≤ getItem s Item.Hat)
  validStock && (totalCost == payment)


inductive Command
  | AddItem (i : Item)
  | DeleteItem (i : Item)
  | ChangeQuantity (i : Item) (q : Nat)
  | QueryCost
  | Checkout (payment : Nat)


/-- | Add_Item  -- 2 rules 1:Returns a new state that is the same as the old state but with the added item 2: returns same state if fails
 | Delete_Item -- Returns a new state that is the same as the old state but without the removed item 2: fails
 | Change_Quantity -- 1: Returns a new state that is the same as the old state but with the modified quantities item 2: returns same state if fails
 | Query_Cost -- Returns the same state
 | Checkout -- 1: Returns the same state if checkout returns false 2: returns empty cart if checkout returns true.
 -/

def operationalSemantics : Command → (ShoppingCart × Stock) → ShoppingCart
  | Command.AddItem i, (sc, s) =>
      match getItem sc i, getItem s i with
      | q, stockQty => if q + 1 ≤ stockQty then setItem sc i (q + 1) else sc

  | Command.DeleteItem i, (sc, _) =>
      match getItem sc i with
      | q => if q > 0 then setItem sc i (q - 1) else sc

  | Command.ChangeQuantity i q, (sc, s) =>
      match getItem s i with
      | stockQty => if q ≤ stockQty then setItem sc i q else sc

  | Command.QueryCost, (sc, _) =>
      sc  -- QueryCost does not modify state

  | Command.Checkout payment, ((q1, q2, q3, q4, q5, q6, q7), (s1, s2, s3, s4, s5, s6, s7)) =>
      let (p1, p2, p3, p4, p5, p6, p7) := (25, 20, 50, 30, 70, 80, 15)
      let totalCost := (q1 * p1 + q2 * p2 + q3 * p3 +
                        q4 * p4 + q5 * p5 + q6 * p6 + q7 * p7)
      let validStock := (q1 ≤ s1) ∧ (q2 ≤ s2) ∧ (q3 ≤ s3) ∧
                        (q4 ≤ s4) ∧ (q5 ≤ s5) ∧ (q6 ≤ s6) ∧ (q7 ≤ s7)
      if validStock && (totalCost == payment) then (0, 0, 0, 0, 0, 0, 0) else (q1, q2, q3, q4, q5, q6, q7)

-- **Test cases**
def testCart : ShoppingCart := (0, 0, 0, 0, 0, 0, 0)
def testStock : Stock := (10, 5, 3, 2, 8, 6, 4)

def test1 := operationalSemantics (Command.AddItem Item.Cotton_Shirt) (testCart, testStock)
def test2 := operationalSemantics (Command.AddItem Item.Jeans) (test1, testStock)
def test3 := operationalSemantics (Command.ChangeQuantity Item.Cotton_Shirt 3) (test2, testStock)
def test4 := getCost test3
def test5 := operationalSemantics (Command.Checkout test4) (test3, testStock)

#eval test1   -- Expected output: (1, 0, 0, 0, 0, 0, 0)
#eval test2   -- Expected output: (1, 0, 1, 0, 0, 0, 0)
#eval test3   -- Expected output: (3, 0, 1, 0, 0, 0, 0)
#eval test4   -- Expected total cost as a Nat
#eval test5   -- Expected output: (0, 0, 0, 0, 0, 0, 0) if checkout succeeds, otherwise same as test3


-- Pretty Printer
def formatCartOrStock (t : ShoppingCart) : List String :=
  let q1 := getItem t Item.Cotton_Shirt
  let q2 := getItem t Item.Polyester_Shirt
  let q3 := getItem t Item.Jeans
  let q4 := getItem t Item.Sweatpants
  let q5 := getItem t Item.Tennis_Shoes
  let q6 := getItem t Item.Running_Shoes
  let q7 := getItem t Item.Hat
  let result := []
  let result := if q1 > 0 then result ++ ["Cotton Shirt x " ++ toString q1] else result
  let result := if q2 > 0 then result ++ ["Polyester Shirt x " ++ toString q2] else result
  let result := if q3 > 0 then result ++ ["Jeans x " ++ toString q3] else result
  let result := if q4 > 0 then result ++ ["Sweatpants x " ++ toString q4] else result
  let result := if q5 > 0 then result ++ ["Tennis Shoes x " ++ toString q5] else result
  let result := if q6 > 0 then result ++ ["Running Shoes x " ++ toString q6] else result
  let result := if q7 > 0 then result ++ ["Hat x " ++ toString q7] else result
  result

-- **Test Cases**
def testCart2 : ShoppingCart := (2, 0, 1, 0, 3, 0, 1)
def testStock2 : Stock := (10, 5, 3, 2, 8, 6, 4)

def testCartFormatted := formatCartOrStock testCart2
def testStockFormatted := formatCartOrStock testStock2

#eval testCartFormatted  -- Expected output: ["Cotton Shirt x 2", "Jeans x 1", "Tennis Shoes x 3", "Hat x 1"]
#eval testStockFormatted -- Expected output: ["Cotton Shirt x 10", "Polyester Shirt x 5", "Jeans x 3", "Sweatpants x 2", "Tennis Shoes x 8", "Running Shoes x 6", "Hat x 4"]

-- If there exists an item in a shopping cart whose quantity is greater than
-- that of the item in a store stock, then the item must be one of the Item
-- constructors.
theorem exists_item_greater_than_stock (sc : ShoppingCart) (s : Stock) :
  (∃ i : Item, getItem sc i > getItem s i) →
    (getItem sc Item.Cotton_Shirt > getItem s Item.Cotton_Shirt) ∨
    (getItem sc Item.Polyester_Shirt > getItem s Item.Polyester_Shirt) ∨
    (getItem sc Item.Jeans > getItem s Item.Jeans) ∨
    (getItem sc Item.Sweatpants > getItem s Item.Sweatpants) ∨
    (getItem sc Item.Tennis_Shoes > getItem s Item.Tennis_Shoes) ∨
    (getItem sc Item.Running_Shoes > getItem s Item.Running_Shoes) ∨
    (getItem sc Item.Hat > getItem s Item.Hat) :=
    by
    intros h
    simp_all
    cases h with
    | intro i hi => cases i with
      | Cotton_Shirt => simp_all
      | Polyester_Shirt => simp_all
      | Jeans => simp_all
      | Sweatpants => simp_all
      | Tennis_Shoes => simp_all
      | Running_Shoes => simp_all
      | Hat => simp_all

-- You cannot check out a cart which contains more items than those available in
-- stock (e.g., if the stock has 2 jeans left, you can't check out 3).
theorem cart_less_than_stock (sc : ShoppingCart) (s : Stock) :
  (¬ ∃ i : Item, getItem sc i > getItem s i) :=
  by sorry

-- you cant add an item to the cart ( or change the number of items) that doesnt correspond to the stock.
theorem no_add_or_change_if_stock_zero (sc : ShoppingCart) (s : Stock) (i: Item)  (q : Nat) :
  getItem s i = 0 →
  (operationalSemantics (Command.AddItem i) (sc, s) = sc ∧
   operationalSemantics (Command.ChangeQuantity i q) (sc, s) = sc) :=
   by sorry

-- if my checkout function (an implementation in lean) evaluates to true then the operational semantics for the Checkout command (specification)
-- evaluates to (0,0,0,0,0,0,0) given the same cart and stock.
theorem checkout_correctness (sc : ShoppingCart) (s : Stock) (payment : Nat) :
  checkout sc payment s = true →
  operationalSemantics (Command.Checkout payment) (sc, s) = (0, 0, 0, 0, 0, 0, 0) :=
 by sorry


-- if you have the items in stock and the customer has enough money to pay for everything then you should able to check out
theorem successful_checkout (sc : ShoppingCart) (s : Stock) (payment : Nat) :
  (∀ i, getItem sc i ≤ getItem s i) → (getCost sc = payment) → checkout sc payment s = true :=
  by sorry
