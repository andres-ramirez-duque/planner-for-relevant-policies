
from parser.action import Action
from parser.formula import *

from itertools import product, chain

DEBUG = False

def flatten(op):
    return _flatten(op.effect)

def combine(eff_lists):
    if DEBUG:
        print "\nCombining:\n%s" % '\n'.join(map(str, eff_lists))
        print "Result: %s\n" % [And(filter(lambda x: x != And([]), list(choice))) for choice in product(*eff_lists)]
    return [And(filter(lambda x: x != And([]), list(choice))) for choice in product(*eff_lists)]

def _flatten(eff):

    if DEBUG:
        print "Flattening %s" % str(eff)

    if isinstance(eff, And):
        if 0 == len(eff.args):
            return [eff]
        else:
            return combine(map(_flatten, eff.args))

    elif isinstance(eff, Oneof):
        return list(chain(*(map(_flatten, eff.args))))
    
    elif isinstance(eff, When):
        return [When(eff.condition, res) for res in _flatten(eff.result)]

    else:
        if DEBUG:
            print "Base: %s" % str(eff)
        return [eff]