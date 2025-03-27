import Init.System.IO
import Init.Data.String.Basic
import Init.Control.Basic

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
deriving BEq
 -- I need this for the sc = newCart.

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


def addItem (sc : ShoppingCart) (s : Stock) (i : Item) : ShoppingCart :=
  let q := getItem sc i
  let stockQty := getItem s i
  if q + 1 ≤ stockQty then setItem sc i (q + 1) else sc

def deleteItem (sc : ShoppingCart) (i : Item) : ShoppingCart :=
  setItem sc i 0

def changeQuantity (sc : ShoppingCart) (s : Stock) (i : Item) (q : Nat) : ShoppingCart :=
  let stockQty := getItem s i
  if q ≤ stockQty then setItem sc i q else sc


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
def EmptyCart : ShoppingCart := (0, 0, 0, 0, 0, 0, 0)
def testStock : Stock := (10, 5, 3, 2, 8, 6, 4)

/--
def test1 := operationalSemantics (Command.AddItem Item.Cotton_Shirt) (EmptyCart, testStock)
def test2 := operationalSemantics (Command.AddItem Item.Jeans) (test1, testStock)
def test3 := operationalSemantics (Command.ChangeQuantity Item.Cotton_Shirt 3) (test2, testStock)
def test4 := getCost test3
def test5 := operationalSemantics (Command.Checkout test4) (test3, testStock)

#eval test1   -- Expected output: (1, 0, 0, 0, 0, 0, 0)
#eval test2   -- Expected output: (1, 0, 1, 0, 0, 0, 0)
#eval test3   -- Expected output: (3, 0, 1, 0, 0, 0, 0)
#eval test4   -- Expected total cost as a Nat
#eval test5   -- Expected output: (0, 0, 0, 0, 0, 0, 0) if checkout succeeds, otherwise same as test3
--/


-- This is the IO part i am trying to implement

def formatCartOrStock (t : ShoppingCart) : List String :=
  let items := [
    (Item.Cotton_Shirt, getItem t Item.Cotton_Shirt),
    (Item.Polyester_Shirt, getItem t Item.Polyester_Shirt),
    (Item.Jeans, getItem t Item.Jeans),
    (Item.Sweatpants, getItem t Item.Sweatpants),
    (Item.Tennis_Shoes, getItem t Item.Tennis_Shoes),
    (Item.Running_Shoes, getItem t Item.Running_Shoes),
    (Item.Hat, getItem t Item.Hat)
  ]
  items.foldl (fun acc (item, qty) =>
    if qty > 0 then acc ++ ["  " ++ toString item ++ " x " ++ toString qty] else acc) []

def displayCart (sc : ShoppingCart) : String :=
  match formatCartOrStock sc with
  | [] => "  Your cart is empty."
  | lst => String.intercalate "\n" lst

def displayStock (s : Stock) : String :=
  String.intercalate "\n" (formatCartOrStock s)



-- I needed to define is as partial because it may not terminate
partial def shoppingLoop (sc : ShoppingCart) (s : Stock) : IO Unit := do
  IO.println "\nCurrent Cart:"
  IO.println (displayCart sc)
  IO.println "\nCurrent Stock:"
  IO.println (displayStock s)
  IO.println "\nEnter a command:\n"
  IO.println "[add]:      This will prompt you to add an item to the cart.\n"
  IO.println "[delete]:   This will prompt you to remove an item from the cart.\n"
  IO.println "[change]:   This will prompt you to change the quantity of an"
  IO.println "            item already in the cart.\n"
  IO.println "[cost]:     This will print the total cost of all the items in"
  IO.println "            the cart.\n"
  IO.println "[checkout]: This will ask you how much money you would like"
  IO.println "            to attempt to checkout with, and then attempt to"
  IO.println "            checkout.\n"
  IO.println "[exit]:     This will exit the shop.\n"
  IO.print "> "

  let stdin ← IO.getStdin

  let input ← stdin.getLine
  let trimmedInput := String.trim input

  match trimmedInput with
  | "add" => do
    IO.println "Enter item name: "
    let itemStr ← stdin.getLine
    let trimmedItem := String.trim itemStr
    let newCart :=
    match trimmedItem with
      | "Cotton Shirt" => addItem sc s Item.Cotton_Shirt
      | "Polyester Shirt" => addItem sc s Item.Polyester_Shirt
      | "Jeans" => addItem sc s Item.Jeans
      | "Sweatpants" => addItem sc s Item.Sweatpants
      | "Tennis Shoes" => addItem sc s Item.Tennis_Shoes
      | "Running Shoes" => addItem sc s Item.Running_Shoes
      | "Hat" => addItem sc s Item.Hat
      | _ => sc -- Leave the cart unchanged
    if sc == newCart then  IO.println (trimmedItem ++ "is not sold at this store. Can't add it to cart") else IO.println (trimmedItem ++ " added to cart.")
    shoppingLoop newCart s

  | "delete" => do
    IO.println "Enter item name: "
    let itemStr ← stdin.getLine
    let trimmedItem := String.trim itemStr
    let newCart :=
    match trimmedItem with
      | "Cotton Shirt" => deleteItem sc Item.Cotton_Shirt
      | "Polyester Shirt" => deleteItem sc Item.Polyester_Shirt
      | "Jeans" => deleteItem sc Item.Jeans
      | "Sweatpants" => deleteItem sc Item.Sweatpants
      | "Tennis Shoes" => deleteItem sc Item.Tennis_Shoes
      | "Running Shoes" => deleteItem sc Item.Running_Shoes
      | "Hat" => deleteItem sc Item.Hat
      | _ => sc -- Leave the cart unchanged
    if sc == newCart then IO.println "There is no such item in your cart" else IO.println (trimmedItem ++ " removed from cart.")
    shoppingLoop newCart s

  | "change" => do
    IO.println "Enter item name: "
    let itemStr ← stdin.getLine
    let trimmedItem := String.trim itemStr
    IO.println "New desired quantity: "
    let numberStr ← stdin.getLine
    let trimmedNumber := String.trim numberStr
    match trimmedNumber.toNat? with
     | some n =>
        let newCart :=
        match trimmedItem with
          | "Cotton Shirt" => changeQuantity sc s Item.Cotton_Shirt n
          | "Polyester Shirt" => changeQuantity sc s Item.Polyester_Shirt n
          | "Jeans" => changeQuantity sc s Item.Jeans n
          | "Sweatpants" => changeQuantity sc s Item.Sweatpants n
          | "Tennis Shoes" => changeQuantity sc s Item.Tennis_Shoes n
          | "Running Shoes" => changeQuantity sc s Item.Running_Shoes n
          | "Hat" => changeQuantity sc s Item.Hat n
          | _ => sc -- Leave the cart unchanged
        if sc == newCart then IO.println ("The store does not have " ++ trimmedNumber ++" "++ trimmedItem ++"in stock. Please select less items") else IO.println (trimmedItem ++ " quantity changed.")
        shoppingLoop newCart s
     | none => IO.println "That is not a valid quantity"
        shoppingLoop sc s
  | "cost" => do
    let currentCost := getCost sc
    IO.println ("The total cost for your cart is: $" ++ toString currentCost)
    shoppingLoop sc s
  | "checkout" => do
    IO.println ("Your total is $" ++ toString (getCost sc) ++". Please input your intended payment:")
    let payment ← stdin.getLine
    let trimmedPayment := String.trim payment
    match trimmedPayment.toNat? with
      | some n => if checkout sc n s then
                    IO.println "Checkout completed successfully!"
                    IO.println "Wait a moment until we restock our inventory."
                  else
                    IO.println "Your payment amount does not match the total cost."
                  let newCart := if  checkout sc n s then (0,0,0,0,0,0,0) else sc
                  shoppingLoop newCart s
      | none => let newCart := sc
                IO.println "Please input a valid dollar amount."
                shoppingLoop newCart s
  | "exit" => IO.println "Goodbye!"
  | _ => do IO.println "Invalid command."; shoppingLoop sc s

-- Main function to start the shopping loop
def main : IO Unit :=
  shoppingLoop EmptyCart testStock
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
  (∃ i : Item, getItem sc i > getItem s i) -> checkout sc payment s = false :=
  by
  intros h
  have one_item_greater_than_stock :
    (getItem sc Item.Cotton_Shirt > getItem s Item.Cotton_Shirt) ∨
    (getItem sc Item.Polyester_Shirt > getItem s Item.Polyester_Shirt) ∨
    (getItem sc Item.Jeans > getItem s Item.Jeans) ∨
    (getItem sc Item.Sweatpants > getItem s Item.Sweatpants) ∨
    (getItem sc Item.Tennis_Shoes > getItem s Item.Tennis_Shoes) ∨
    (getItem sc Item.Running_Shoes > getItem s Item.Running_Shoes) ∨
    (getItem sc Item.Hat > getItem s Item.Hat) :=
    by exact exists_item_greater_than_stock sc s h
  rw [checkout]
  simp_all
  intros
  cases one_item_greater_than_stock with
  | inr rhs => cases rhs with
    | inr rhs => cases rhs with
      | inr rhs => cases rhs with
        | inr rhs => cases rhs with
          | inr rhs => cases rhs with
            | inr hat => rewrite [Nat.lt_iff_le_and_not_ge] at hat; simp_all
            | inl running_shoes =>
              rewrite [Nat.lt_iff_le_and_not_ge] at running_shoes
              simp_all
          | inl tennis_shoes =>
            rewrite [Nat.lt_iff_le_and_not_ge] at tennis_shoes;
            simp_all
        | inl sweatpants => rewrite [Nat.lt_iff_le_and_not_ge] at sweatpants
                            simp_all
      | inl jeans => rewrite [Nat.lt_iff_le_and_not_ge] at jeans; simp_all
    | inl polyester_shirt =>
      rewrite [Nat.lt_iff_le_and_not_ge] at polyester_shirt
      simp_all
  | inl cotton_shirt => rewrite [Nat.lt_iff_le_and_not_ge] at cotton_shirt
                        simp_all

-- You can't add an item to the cart, or set its quantity to a nonzero value, if
-- that item is not in stock.
theorem no_add_or_change_if_stock_zero
  (sc : ShoppingCart) (s : Stock) (i: Item) (q : Nat) :
  (getItem s i = 0 ∧
  -- We need this clause because otherwise q could itself be zero, and changing
  -- the item's quantity would then be allowed.
  q > 0) →
  (operationalSemantics (Command.AddItem i) (sc, s) = sc ∧
   operationalSemantics (Command.ChangeQuantity i q) (sc, s) = sc) :=
  by
  intros H0
  have H1 := H0.left
  have H2 := H0.right
  have left : operationalSemantics (Command.AddItem i) (sc, s) = sc :=
    by
    rw [operationalSemantics]
    simp
    rw [H1]
    simp
  have right : operationalSemantics (Command.ChangeQuantity i q) (sc, s) = sc :=
    by
    rw [operationalSemantics]
    simp
    rw [H1]
    intro contra
    simp_all
  simp_all

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
