import sys
sys.setrecursionlimit(1000000)

n, m = map(int, raw_input().split())
r  = float('inf')
dp = {}

def dfs(a):
  global dp, visitado, n, m 

  if a > m   : return a - m  
  if a < 0   : return float('inf')
  if a == m  : return 0
  if a in dp : return dp[a] 

  dp[a] = float('inf')
  dp[a] = 1 + min(dfs(a*2), dfs(a -1))
  return dp[a]

print dfs(n)

