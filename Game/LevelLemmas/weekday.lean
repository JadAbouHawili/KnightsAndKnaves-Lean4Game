inductive Weekday where
  | sunday
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
deriving Repr
open Weekday

namespace Weekday
def next (d : Weekday) : Weekday :=
 match d with
 | sunday    => monday
 | monday    => tuesday
 | tuesday   => wednesday
 | wednesday => thursday
 | thursday  => friday
 | friday    => saturday
 | saturday  => sunday
def previous (d : Weekday) : Weekday :=
 match d with
 | sunday    => saturday
 | monday    => sunday
 | tuesday   => monday
 | wednesday => tuesday
 | thursday  => wednesday
 | friday    => thursday
 | saturday  => friday

def next_previous (d : Weekday) : next (previous d) = d := by
  cases d <;> rfl

def numberOfDay (d : Weekday) : Nat :=
match d with
  | sunday    => 1
  | monday    => 2
  | tuesday   => 3
  | wednesday => 4
  | thursday  => 5
  | friday    => 6
  | saturday  => 7


example(d : Weekday) :2=2 := by
    cases d
    repeat sorry
