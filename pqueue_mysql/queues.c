// A priority queue implementation from MySQL 5.7
// The original version is at https://raw.githubusercontent.com/mysql/mysql-server/21e162518cf72802e295d0858ce59edd1d455218/mysys/queues.c

/* Copyright (c) 2000, 2015, Oracle and/or its affiliates. All rights reserved.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; version 2 of the License.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301  USA */

/*
  Code for handling of priority Queues.
  Implemention of queues from "Algoritms in C" by Robert Sedgewick.
  An optimisation of _downheap suggested in Exercise 7.51 in "Data
  Structures & Algorithms in C++" by Mark Allen Weiss, Second Edition
  was implemented by Mikael Ronstrom 2005. Also the O(N) algorithm
  of queue_fix was implemented.
*/

#include "queues.h"

#include <stdlib.h>
#include <assert.h>

#define DBUG_ENTER(s)
#define DBUG_RETURN(e) return (e)
#define DBUG_VOID_RETURN return
#define DBUG_ASSERT assert

typedef char    my_bool;
#define TRUE 1
#define FALSE 0
#define set_if_smaller(a,b) { if ((a) > (b)) (a)=(b); }

	/* Remove item from queue */
	/* Returns pointer to removed element */

int queue_remove(QUEUE *queue, uint idx)
{
  int element;
  DBUG_ASSERT(idx < queue->max_elements);
  element= queue->root[++idx];  /* Intern index starts from 1 */
  queue->root[idx]= queue->root[queue->elements--];
  _downheap(queue, idx);
  return element;
}


void _downheap(QUEUE *queue, uint idx)
{
  int element;
  uint elements,half_queue, next_index;
  my_bool first= TRUE;
  uint start_idx= idx;

  element=queue->root[idx];
  half_queue=(elements=queue->elements) >> 1;

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
    queue->root[idx]=queue->root[next_index];
    idx=next_index;
    first= FALSE;
  }

  next_index= idx >> 1;
  while (next_index > start_idx)
  {
    if (queue->root[next_index] < element)
      break;
    queue->root[idx]=queue->root[next_index];
    idx=next_index;
    next_index= idx >> 1;
  }
  queue->root[idx]=element;
}
