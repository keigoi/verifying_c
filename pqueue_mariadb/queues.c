// A priority queue implementation from MariaDB 10.3.
// Downloaded from https://github.com/MariaDB/server/raw/7be541f281225aae8e04bff4210b67688be080bc/mysys/queues.c

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
  This code originates from the Unireg project.

  Code for generell handling of priority Queues.
  Implementation of queues from "Algorithms in C" by Robert Sedgewick.

  The queue can optionally store the position in queue in the element
  that is in the queue. This allows one to remove any element from the queue
  in O(1) time.

  Optimisation of _downheap() and queue_fix() is inspired by code done
  by Mikael Ronström, based on an optimisation of _downheap from
  Exercise 7.51 in "Data Structures & Algorithms in C++" by Mark Allen
  Weiss, Second Edition.
*/

#include "queues.h"

typedef char    my_bool;
#define TRUE 1
#define FALSE 0

/*
  Add element to fixed position and update heap

  SYNOPSIS
    _downheap()
    queue	Queue to use
    idx         Index of element to change
    element     Element to store at 'idx'

  NOTE
    This only works if element is >= all elements <= start_idx
*/

void _downheap(QUEUE *queue, uint start_idx, int element)
{
  uint elements,half_queue, next_index;
  register uint idx= start_idx;
  my_bool first= TRUE;

  half_queue= (elements= queue->elements) >> 1;

  while (idx <= half_queue)
  {
    next_index=idx+idx;
    if (next_index < elements &&
        queue->root[next_index] > queue->root[next_index+1])
      next_index++;
    if (first &&
	queue->root[next_index] >= element)
    {
      queue->root[idx]= element;
      return;
    }
    first= FALSE;
    queue->root[idx]= queue->root[next_index];
    idx=next_index;
  }

  /*
    Insert the element into the right position. This is the same code
    as we have in queue_insert()
  */
  while ((next_index= (idx >> 1)) > start_idx &&
         element < queue->root[next_index])
  {
    queue->root[idx]= queue->root[next_index];
    idx= next_index;
  }
  queue->root[idx]= element;
}


