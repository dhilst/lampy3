import re;
from operator import truth;

def fact x : forall, int -> int =
    if x == 0
    then 1
    else x * fact (x - 1);;

def id y : forall a, a -> a =
    y;;

type truth = forall a, a -> bool;
type re.match = forall, string -> re.Match;

def test () : forall, unit -> unit =
    assert (fact 5 == 120);
    assert (id 1 == 1);
    assert (truth 1 == true);
    assert (truth "" == false);
    ();;
