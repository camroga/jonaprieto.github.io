n = int(raw_input())
x = [int(raw_input()) for _ in range(n)]

ans = 0
for i in range(n):
  d = 1
  while x[i] > -1:
    d += 1
    i = x[i] - 1
  ans = max(ans, d)
print ans  

