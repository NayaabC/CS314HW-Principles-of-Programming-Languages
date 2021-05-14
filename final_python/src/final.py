from prolog_structures import Rule, RuleBody, Term, Function, Variable, Atom, Number
from typing import List
from functools import reduce

import sys
import random

class Not_unifiable(Exception):
	pass

'''
Please read prolog_structures.py for data structures
that represent Prolog terms, rules, and goals.
'''
class Interpreter:
	def __init__(self):
		pass

	'''
	Example
	occurs_check (v, t) where v is of type Variable, t is of type Term.
	occurs_check (v, t) returns true if the Prolog Variable v occurs in t.
	Please see the lecture note Control in Prolog to revisit the concept of
	occurs-check.
	'''
	def occurs_check (self, v : Variable, t : Term) -> bool:
		if isinstance(t, Variable):
			return v == t
		elif isinstance(t, Function):
			for t in t.terms:
				if self.occurs_check(v, t):
					return True
			return False
		return False


	'''
	Problem 1
	variables_of_term (t) where t is of type Term.
	variables_of_clause (c) where c is of type Rule.

	The function should return the Variables contained in a term or a rule
	using Python set.

	The result must be saved in a Python set. The type of each element (a Prolog Variable)
	in the set is Variable.
	'''
	def variables_of_term (self, t : Term) -> set :
		s1 = set()
		s2 = set()
		if isinstance(t, Variable):
			s1.add(t)
		elif isinstance(t, Function):
			for t in t.terms:
				if isinstance(t, Variable):
					s2.add(t)
				elif isinstance(t, Function):
					s1 = self.variables_of_term(t)
				self.variables_of_term(t)
		s3 = s1.union(s2)
		#print(s3)
		return s3

	def variables_of_clause (self, c : Rule) -> set :
		s1 = set()
		s2 = set()
		x = c.body
		#print(c.__str__())
		for c in c.head.terms:
			if isinstance(c, Variable):
				s1.add(c)
		
		for b in x.terms:
			if isinstance(b, Variable):
				s2.add(b)
		#print(s1)

		return s1.union(s2)


	'''
	Problem 2
	substitute_in_term (s, t) where s is of type dictionary and t is of type Term
	substitute_in_clause (s, t) where s is of type dictionary and c is of type Rule,

	The value of type dict should be a Python dictionary whose keys are of type Variable
	and values are of type Term. It is a map from variables to terms.

	The function should return t_ obtained by applying substitution s to t.

	Please use Python dictionary to represent a subsititution map.
	'''
	def substitute_in_term (self, s : dict, t : Term) -> Term:
		fin = set()
		if isinstance(t, Function):
			new_terms = []
			for term in t.terms:
				new_terms.append(s.get(term)) if term in s.keys() else new_terms.append(term)
				
			fin = Function(t.relation, new_terms)
		else:
			if t in s.keys():
				fin = s.get(t)
			else:
				fin = t
		return fin


	def substitute_in_clause (self, s : dict, c : Rule) -> Rule:
		fin = set()
		fin2 = []
		if isinstance(c.head, Function):
			new_terms = []
			for term in c.head.terms:
				new_terms.append(s.get(term)) if term in s.keys() else new_terms.append(term)
			
			fin = Function(c.head.relation, new_terms)
		elif isinstance(c.head, Variable):
			fin = Function(c.head.relation, s.get(c.head))
		
		if isinstance(c.body, Function):
			new_terms = []
			for term in c.body.terms:
				new_terms.append(s.get(term)) if term in s.keys() else new_terms.append(term)
			
			fin2 = Function(c.body.relation, new_terms)
		elif isinstance(c.body.terms, Variable):
			fin2 = Function(c.body.relation, s.get(c.body))
		
		if not fin2:
			ans = Rule(fin, c.body)
		else:
			ans = Rule(fin, RuleBody(fin2))
		return ans


	'''
	Problem 3
	unify (t1, t2) where t1 is of type term and t2 is of type Term.
	The function should return a substitution map of type dict,
	which is a unifier of the given terms. You may find the pseudocode
	of unify in the lecture note Control in Prolog useful.

	The function should raise the exception raise Not_unfifiable (),
	if the given terms are not unifiable.

	Please use Python dictionary to represent a subsititution map.
	'''
	def unify (self, t1: Term, t2: Term) -> dict:
		def unification(t1: Term, t2: Term, sig: dict):
			x = self.substitute_in_term(sig, t1)
			y = self.substitute_in_term(sig, t2)
			if isinstance(x, Variable) and (not self.occurs_check(x, y)):
				for k in sig.keys():
					sig[k] = self.substitute_in_term({x : y}, sig[k])
				sig[x] = y
				return sig
			elif isinstance(y, Variable) and not self.occurs_check(y, x):
				for k in sig.keys():
					sig[k] = self.substitute_in_term({y : x}, sig[k])
				sig[y] = x
				return sig
			elif x == y:
				return sig
			elif isinstance(x, Function) and isinstance(y, Function):
				if len(x.terms) != len(y.terms):
					raise Not_unifiable()
				else:
					for tx, ty in zip(x.terms, y.terms):
						res = unification(tx, ty, sig)
					return res

			else:
				raise Not_unifiable()
				



		fin = unification(t1, t2, {})
		#print("Fin: ", fin)
		return fin






	#FOR PROBLEM 4
	fresh_counter = 0
	def fresh(self) -> Variable:
		self.fresh_counter += 1
		return Variable("_G" + str(self.fresh_counter))
	def freshen(self, c: Rule) -> Rule:
		c_vars = self.variables_of_clause(c)
		theta = {}
		for c_var in c_vars:
			theta[c_var] = self.fresh()

		return self.substitute_in_clause(theta, c)


	'''
	Problem 4
	Following the Abstract interpreter pseudocode in the lecture note Control in Prolog to implement
	a nondeterministic Prolog interpreter.

	nondet_query (program, goal) where
		the first argument is a program which is a list of Rules.
		the second argument is a goal which is a list of Terms.

	The function returns a list of Terms (results), which is an instance of the original goal and is
	a logical consequence of the program. See the tests cases (in src/main.py) as examples.
	'''
	def nondet_query (self, program : List[Rule], pgoal : List[Term]) -> List[Term]:
		# res = pgoal
		# while res:
		# 	selection = random.randint(0, len(pgoal))
		# 	a = pgoal[selection]
		# 	self.unify(program, a)
		goal = []
		while(True):
			goal = pgoal
			res = goal

			while res:
				selection = random.randint(0, len(goal))
				rand_rule = random.randint(0, len(program))
				rand_rule = self.freshen(rand_rule)

				try:
					sig = self.unify(selection, rand_rule.head)
				except:
					break
					
				res.remove(selection)

				for term in rand_rule.body.terms:
					res.append(term)
				
				fin = {}
				for term in res:
					fin[term] = self.substitute_in_term(sig, term)
				res = fin

				fgoal = {}
				for term in goal:
					fgoal[term] = self.substitute_in_term(sig, term)
				goal = fgoal

				if res:
					continue
				else:
					break
		return goal


	'''
	Challenge Problem

	det_query (program, goal) where
		the first argument is a program which is a list of Rules.
		the second argument is a goal which is a list of Terms.

	The function returns a list of term lists (results). Each of these results is
	an instance of the original goal and is a logical consequence of the program.
	If the given goal is not a logical consequence of the program, then the result
	is an empty list. See the test cases (in src/main.py) as examples.
	'''
	def det_query (self, program : List[Rule], pgoal : List[Term]) -> List[List[Term]]:
		return [pgoal]
