import sys

from action import Action
from formula import Primitive, Forall, When, And, Not
from predicate import Predicate

LOG=False

class StaticsBasedGrounder:

    def __init__(self, GP):
        self.GP = GP
        self.statics=None
        self.fluent_dict=None


    def _initiateGroundingUsingStatics(self, static_precs, params, flags, combs, s) :

        for static_prec in static_precs:
            newCombs = []
            generatorPropositions = map(lambda p: p.predicate, self._getRelevantProps(static_prec, s))
            for existingProposition in generatorPropositions :
                for c in combs :
                    ok = True
                    for propositionArgPos in range(len(static_prec.args)) :
                        opArgID = params.index(static_prec.args[propositionArgPos])
                        if flags[opArgID] :
                            if not c[opArgID] == existingProposition.args[propositionArgPos]:
                                ok = False
                                break
                    if ok :
                        newComb = c[:]
                        for propositionArgPos in range(len(static_prec.args)) :
                            opArgID = params.index(static_prec.args[propositionArgPos])
                            newComb[opArgID] = existingProposition.args[propositionArgPos]
                        newCombs.append(newComb)

            combs = newCombs

            for propositionArgPos in range(len(static_prec.args)) :
                opArgID = params.index(static_prec.args[propositionArgPos])
                flags[opArgID] = True
        return combs
    

    def _getRelevantProps(self, pSym, s) :
        return filter(lambda p: p.predicate.name == pSym.name, s)
    
    def _note_static_preconditions(self, formula, static_precs):
        if formula is None:
            pass
        elif isinstance(formula, Primitive):
            if formula.predicate.name in self.statics:
                static_precs.append(formula.predicate)
        elif isinstance(formula, Not):
            pass # This is probably only helpful after filling all args - not much benefit by then..
        elif isinstance(formula, Forall):
            for arg in formula.args:
                self._note_static_preconditions(arg, static_precs)
        elif isinstance(formula, When):
            pass
        elif isinstance(formula, And):
            for arg in formula.args:
                self._note_static_preconditions(arg, static_precs)
        else:
            pass
        
    def fill_in_combinations(self, a, nextcombs, flags):
      vars = map(lambda i: a.parameters[i], filter(lambda i: not flags[i], range(len(a.parameters))))
      flagged_var_names = map(lambda i: a.parameters[i][0], filter(lambda i: flags[i] ,range(len(flags))))
      var_names, val_generator = self.GP._create_valuations(vars)
      for valuation in val_generator:
          assignment = {var_name: val for var_name, val in zip(var_names, valuation)}
          if LOG:
              print assignment
          for coomb in nextcombs:
              next_assignment = assignment.copy()
              for (k,v) in zip(flagged_var_names,map(lambda i: coomb[i], filter(lambda i: flags[i] ,range(len(flags))))) :
                  next_assignment[k]=v[0]
              if LOG:
                  print next_assignment, 
              self.ground_actions.add(self.GP._action_to_operator(a, next_assignment, self.fluent_dict))
                  
    def ground_action(self, a):    
        dummyPs = [None]*len(a.parameters)
        flags = [False]*len(a.parameters)
        static_precs = []
        self._note_static_preconditions(a.precondition, static_precs)
        params = map(lambda (o,t): o, a.parameters)
        nextcombs = self._initiateGroundingUsingStatics(static_precs, a.parameters, flags, [dummyPs], self.GP.init.args)
        self.fill_in_combinations(a, nextcombs, flags)

    def note_effected_predicates(self, formula, dynamic_predicates):
        if formula is None:
            pass
        elif isinstance(formula, Primitive):
            dynamic_predicates.append(formula.predicate.name)
        elif isinstance(formula, Forall):
            for arg in formula.args:
                self.note_effected_predicates(arg, dynamic_predicates)
        elif isinstance(formula, When):
            return self.note_effected_predicates(formula.result, dynamic_predicates)
        else:
            for arg in formula.args:
                self.note_effected_predicates(arg, dynamic_predicates)

    def _find_statics(self):
        dynamic_predicates = []
        for action in self.GP.actions:
            self.note_effected_predicates(action.effect, dynamic_predicates)
        self.statics = []
        for predicate in self.GP.predicates:
            if not predicate.name in dynamic_predicates:
                self.statics.append(predicate.name)
    
    def _create_operators(self):
        self.ground_actions = set([])

        for a in self.GP.actions:
          self.ground_action(a)
    
    def _create_fluents(self):
        """Create the set of fluents by grounding the predicates."""

        self.GP.fluents = set([])
        for p in self.GP.predicates:
            var_names, val_generator = self.GP._create_valuations(p.args)
            for valuation in val_generator:
                assignment = {var_name: val for var_name, val in zip(var_names, valuation)}
                self.GP.fluents.add(self.GP._predicate_to_fluent(p, assignment))
        
    def ground_actions(self):
        self._find_statics()
        if LOG:
            print "\n\n\n\n==== STATIC BASED GROUNDER ================================================================"
            print self.statics
        
        
        self._create_fluents()

        # to avoid creating a bunch new fluent objects, create a dictionary mapping fluent names to their objects
        self.fluent_dict = {hash(f): f for f in self.GP.fluents}

        self._create_operators()
        self.GP.operators = self.ground_actions
        self.GP._ground_init(self.fluent_dict)
        if LOG:
            print self.ground_actions
            print len (self.ground_actions)
            print "====================================================================\n\n\n\n"
        
