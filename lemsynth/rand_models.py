import random

#All implementations in this file are outdated. Must be updated to use the format of dictionaries indexed by signature
def oneRandModel(elems, fcts):
  num_fcts = len(fcts)
  num_elems = len(elems)
  choices = random.choices(elems,k = num_elems*num_fcts)
  res = {tuple([(fcts[i],elems[j],choices[j*num_fcts + i]) for i in range(num_fcts) for j in range(num_elems)])}
  return res

def genRandModels(elems, fcts, num):
  models = set()
  while len(models) != num:
    models = models.union(oneRandModel(elems, fcts))
  return [list(model) for model in models]

#randmodels = genRandModels(range(2),['next'],4)
#big_randmodels = genRandModels(range(5),fcts,100) #corresponding call with genModels times out
