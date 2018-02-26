// A priority queue implementation from MariaDB 10.3.
// Downloaded from https://github.com/MariaDB/server/raw/4aaa38d26ed95127b8424100c8a14c77af15fc11/include/queues.h

/* Copyright (C) 2010 Monty Program Ab
   All Rights reserved

   Redistribution and use in source and binary forms, with or without
   modification, are permitted provided that the following conditions are met:
    * Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the following disclaimer
      in the documentation and/or other materials provided with the
      distribution.

  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
  FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL
  <COPYRIGHT HOLDER> BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF
  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT
  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
  SUCH DAMAGE.
*/

/*
  Code for generell handling of priority Queues.
  Implemention of queues from "Algoritms in C" by Robert Sedgewick.
*/

#ifndef _queues_h
#define _queues_h

#ifdef	__cplusplus
extern "C" {
#endif

typedef unsigned int uint;

typedef struct st_queue {
  int *root;
  uint elements;
  uint max_elements;
} QUEUE;

void _downheap(QUEUE *queue, uint idx, int element);

#ifdef	__cplusplus
}
#endif
#endif
