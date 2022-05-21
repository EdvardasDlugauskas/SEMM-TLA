# Shared memory from message passing

## Attiya, Bar-Noy, and Dolev algorithm

ACM: https://dl.acm.org/doi/10.1145/200836.200869

Book: https://www.cs.yale.edu/homes/aspnes/pinewiki/SharedMemoryVsMessagePassing.html

### Requirements (abstract spec)
- We have N processes, they form a complete network
- Each process has a register that holds a value
- One of N processes writes a value
  - The writer waits for the write operation to complete
  - After a successful write, either the written value or a newer value is returned

### Algorithm

Here `u` - nonce, `v` - value of a process register, `t` - timestamp.

**Write**:
1. Send `read(u)` to all processes
2. Wait until acknowledgement from a majority is received
3. Set my `t` to `(max t + 1, id)`
4. Send `write(v, t)` to all processes, wait for a response `ack(v, t)` from a majority of processes

**Read**:
1. Send `read(u)` to all processes, wait for acknowledgment from majority. 
2. The `v` with the maximum associated `t` becomes the return value.
3. Send `write(v, t)` to all processes, wait for `ack(v, t)` from the majority. 
4. Return `v`.