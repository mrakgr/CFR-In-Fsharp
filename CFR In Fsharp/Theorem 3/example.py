# Python version of the F# counter example.

class Terminal: 
	def __init__(self, reward): self.reward = reward

class Response:
	def __init__(self, id, branches): 
		self.id = id
		self.branches = branches

def u(o,tree):
	if tree.__class__ is Terminal: return tree.reward
	else: return sum([policy * u(o,branch) for (policy,branch) in zip(o[tree.id],tree.branches)])

def R_full(o_new,o,tree): return u(o_new,tree) - u(o,tree)

def update_at_branch_current(cur,next,tree):
	if tree.__class__ is Terminal: return cur
	else: 
		cur = cur.copy()
		cur[tree.id] = next[tree.id]
		return cur

def R_imm(o_new,o,tree): return max(0, u(update_at_branch_current(o,o_new,tree),tree) - u(o,tree))
def R_imm_sum(o_new,o,tree):
	if tree.__class__ is Terminal: return 0
	else: return R_imm(o_new,o,tree) + sum([R_imm_sum(o_new,o,branch) for branch in tree.branches])

o = { 0:[1,0], 1:[1,0], 2:[0,1] }
o_new = { 0:[0,1], 1:[0,1], 2:[0,1] }
tree = Response(0,[Terminal(-10), Response(1,[Response(2,[Terminal(10), Terminal(-10)]),Terminal(10)])])

print(R_full(o_new,o,tree)) # 20
print(R_imm_sum(o_new,o,tree)) 

# Hence R_full <= R_imm_sum as per theorem 3 is false.