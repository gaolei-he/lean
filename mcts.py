#!/usr/bin/env python
# -*- coding: utf-8 -*-
# Paper from http://pubs.doc.ic.ac.uk/survey-mcts-methods/survey-mcts-methods.pdf .

import sys
import math
import random
import numpy as np
from transformers import AutoTokenizer, AutoModelForSeq2SeqLM
from lean_dojo import *
import ssl
ssl._create_default_https_context = ssl._create_unverified_context
import torch
import torch.nn as nn
import torch.nn.functional as F
import torch.optim as optim
TACRIC_NUMBER = 4
MAX_ROUND_NUMBER = 10

# repo = LeanGitRepo("https://github.com/yangky11/lean4-example", "a61b40b90afba0ee5a3357665a86f7d0bb57461d")
# theorem = Theorem(repo, "idt_2.lean", "idt2")

# repo = LeanGitRepo(
#     "https://github.com/Moyvbai/lean4-example",
#     "87f9ea9a9d7cbc6dd9e116e04234c032720ca8dc",
# )
# theorem = Theorem(repo, "Lean4Example.lean", "idt1_Pascal's_Recurrence")
 
# repo = LeanGitRepo("https://github.com/Lei085400/lean4-example", "a61b40b90afba0ee5a3357665a86f7d0bb57461d")
# theorem = Theorem(repo, "Lean4Example.lean", "hello_world")
repo = LeanGitRepo(
    "https://github.com/Moyvbai/lean4-example",
    "87f9ea9a9d7cbc6dd9e116e04234c032720ca8dc",
)
theorem = Theorem(repo, "Lean4Example.lean", "idt1_Pascal's_Recurrence")
feature_size = 70
dojo, state11 = Dojo(theorem).__enter__()

# print("证明目标：")
# print(state)

tokenizer = AutoTokenizer.from_pretrained("/home2/wanglei/python_project/leandojo-lean4-tacgen-byt5-small")       # Or "lean3" -> "lean4"
model = AutoModelForSeq2SeqLM.from_pretrained("/home2/wanglei/python_project/leandojo-lean4-tacgen-byt5-small")   # Or "lean3" -> "lean4"

def encode_state(state):
    encode_state = tokenizer.encode(str(state))
    if(len(encode_state)<=feature_size):
        encode_state += [0]*(feature_size-len(encode_state))  #list
    else:
        encode_state = encode_state[:feature_size]
    # print("encode")
    # print(encode_state)
    return encode_state

def encode_tactic(tactic):
    encode_tactic = tokenizer.encode(str(tactic))
    if(len(encode_tactic)<=feature_size):
        encode_tactic += [0]*(feature_size-len(encode_tactic))
    else:
        encode_tactic = encode_tactic[:feature_size]
    return encode_tactic

# def tactic_generator(state):
#     init_state = state.pp
#     tokenized_state = tokenizer(init_state, return_tensors="pt")

#     # Generate multiple tactics via beam search.
#     tactic_candidates_ids = model.generate(
#         tokenized_state.input_ids,
#         max_length=1024,
#         num_beams=4,
#         length_penalty=0.0,
#         do_sample=False,
#         num_return_sequences=4,
#         early_stopping=False,
#     )
#     tactic_candidates = tokenizer.batch_decode(
#         tactic_candidates_ids, skip_special_tokens=True
#     )
#     return tactic_candidates

def tactic_generator(state):
  # tactic_candidates = ['rw [Nat.add_comm]',
  #                      'rw [Nat.add_assoc]', 
  #                      'rw [Nat.add_comm b c]', 
  #                      'rw [Nat.add_comm c b]',
  #                      ]
  # tactic_candidates = [
  #                       'apply choose_symm_of_eq_add',
  #                       'rw [add_comm m 1]',
  #                       'rw [add_assoc 1 m m]',
  #                       'rw [add_comm (2 * m) 1]',
  #                       'rw [two_mul m]',
  #                       'rw [mul_assoc]'
  #                       ]
  # tactic_candidates = ['induction n <;> ',
  #                       'simp [*, choose]' ,
  #                       'rw [Nat.add_assoc]', 
  #                       'simp [add_comm]']
  tactic_candidates = [ 'have choose_eq_choose_sub_add :  choose n k = choose (n - 1 + 1) (k - 1 + 1)  := by rw[Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]',
                        'rw[choose_eq_choose_sub_add,add_comm (choose (n - 1) k) (choose (n - 1) (k - 1))]',
                        'have choose_sub_eq_choose_sub_add : choose (n - 1) k = choose (n - 1) (k - 1 + 1) := by rw[Nat.sub_add_cancel h2]',
                        'rw[choose_sub_eq_choose_sub_add, choose_succ_succ]']
  return tactic_candidates


class State(object):
  
  def __init__(self,state):
    self.tac = None  #记录当前状态是通过哪个策略得到的
    self.state = state

  def is_terminal(self):  ############# 更改为 证明是否完成（证明成功or失败）
    return self.state== 1 or self.state == -1

  def compute_reward(self):   ############# 证明成功为1，失败为0
    if (self.state == 1):
      return 1
    elif (self.state == -1):
      return 0
    else:
      return None
  
  def proof(self,state,tac):
      result = dojo.run_tac(state, tac)
      # print("当前状态为{}".format(state))
      # print("策略为{}".format(tac))
      try:
          if(result.error is not None):  ## 证明失败，terminal = 1 ， reward = -1
              # print("证明失败")
              return -1
      except Exception as ex: 
          if(result == ProofGivenUp()):
              print(result)
              # print(dojo.is_successful)
              # print("证明放弃，terminal = 1 ， reward = -1")
              return -1
          else:
              try:
                  if(result.pp is not None):
                      # print(result)
                      # # print(dojo.is_successful)
                      # print("证明未完成，terminal = 0 ， reward = 0")
                      return result
              except Exception as ex:
                  if(dojo.is_successful == True): ## 证明成功
                      # print(result)
                      # # print(dojo.is_successful)
                      # print("证明成功，terminal = 1 ， reward = 1")
                      return 1

  def get_next_state_with_random_choice(self):  ############# 根据当前state输入大模型，获取策略list后，随机选择其中一个策略，返回执行该随机策略后的状态
    tactic_candidates = tactic_generator(self.state)
    random_choice = random.choice([choice for choice in tactic_candidates])
    next_state = self.proof(self.state,random_choice)
    next_state = State(next_state)
    next_state.tac = random_choice
    # next_state = proof(self.state,random_choice)
    # next_node = Node()
    # next_node.set_state(next_state)
    # next_node.tac = random_choice
    return next_state

class Node(object):
  """
  蒙特卡罗树搜索的树结构的Node，包含了父节点和直接点等信息，还有用于计算UCB的遍历次数和quality值，还有游戏选择这个Node的State。
  """

  def __init__(self):
    self.parent = None
    self.children = []
    self.prob = 0

    self.visit_times = 0
    self.quality_value = 0.0

    self.state = None
    
    self.depth = 0 

  def set_state(self, state):
    self.state = state

  def get_state(self):  
    return self.state

  def set_parent(self, parent):  
    self.parent = parent

  def get_children(self):  
    return self.children

  def get_visit_times(self):  
    return self.visit_times

  def visit_times_add_one(self):  
    self.visit_times += 1

  def get_quality_value(self): 
    return self.quality_value

  def quality_value_add_n(self, n):  
    self.quality_value += n

  def is_all_expand(self): #### 判断该状态下，是否所有的list中的策略都尝试过了
    return len(self.children) == TACRIC_NUMBER

  def add_child(self, sub_node):
    sub_node.set_parent(self)
    self.children.append(sub_node)
  
  def select_action(self):
    """
    Select action according to the visit count distribution and the temperature.
    """
    visit_counts = np.array([child.visit_times for child in self.children])
    actions = [action for action in self.children.state.tac]
    action = actions[np.argmafx(visit_counts)]
    return action


  def __repr__(self):
    return "Node: {}, Q/N: {}/{}, state: {}".format(
        hash(self), self.quality_value, self.visit_times, self.state)


class MCTS:

    def __init__(self, node, policy_model, value_model, args):
        self.node = node
        self.policy_model = policy_model
        self.value_model = value_model
        self.args = args

    def tree_policy(self, node):
      """
      蒙特卡罗树搜索的Selection和Expansion阶段，传入当前需要开始搜索的节点（例如根节点），根据exploration/exploitation算法返回最好的需要expend的节点，注意如果节点是叶子结点直接返回。

      基本策略是先找当前未选择过的子节点，如果有多个则随机选。如果都选择过就找权衡过exploration/exploitation的UCB值最大的，如果UCB值相等则随机选。
      """

      # Check if the current node is the leaf node
      while node.state.is_terminal() == False:

        if node.is_all_expand():
          node = self.best_child(node, True)

        else:
          # Return the new sub node
          sub_node = self.expand(node)
          return sub_node

      # Return the leaf node
      return node


    def default_policy(self,node):
      """
      蒙特卡罗树搜索的Simulation阶段，输入一个需要expand的节点，随机操作后创建新的节点，返回新增节点的reward。注意输入的节点应该不是子节点，而且是有未执行的Action可以expend的。

      基本策略是随机选择Action。
      """

      # # Get the state of the game
      # current_state = node.get_state()

      # Run until the game over

      state = node.state

      while state.is_terminal() == False:

        # Pick one random action to play and get next state
        state = state.get_next_state_with_random_choice()
        
      
      final_state_reward = state.compute_reward()
      return final_state_reward


    def expand(self,node):
      """
      输入一个节点，在该节点上拓展一个新的节点，使用random方法执行Action，返回新增的节点。注意，需要保证新增的节点与其他节点Action不同。
      """

      tried_sub_node_states = [     # 统计node已经展开的所有子节点
          sub_node.get_state().state for sub_node in node.get_children()
      ]
      
      tried_sub_node_tacs = [     # 统计node已经展开的所有子节点
          sub_node.get_state().tac for sub_node in node.get_children()
      ]

      new_state = node.state.get_next_state_with_random_choice()   # 根据当前node状态随机采取action，获得执行后的新状态

      # Check until get the new state which has the different action from others
      while new_state.state in tried_sub_node_states and new_state.tac in tried_sub_node_tacs:  # 判断新状态是否已经被expand，若已经被expand，则重新对node随机采取action，获得新状态
        new_state = node.state.get_next_state_with_random_choice()   # 根据当前node状态随机采取action，获得执行后的新状态
      
      new_node = Node()
      new_node.set_state(new_state)
      new_node.depth = node.depth + 1
      #########################
      encodestate = encode_state(node.state.state)
      encodetactic = encode_tactic(new_state.tac)
      input_policy = encodestate + encodetactic
      input_policy = torch.FloatTensor(np.array(input_policy).astype(np.float64))
      new_node.prob = float(self.policy_model(input_policy))  # 返回的应该不是值，而是数组？
      #########################
      node.add_child(new_node)

      return new_node


    def best_child(self, node, is_exploration):
      """
      使用UCB算法，权衡exploration和exploitation后选择得分最高的子节点，注意如果是预测阶段直接选择当前Q值得分最高的。
      """

      # TODO: Use the min float value
      best_score = -sys.maxsize
      best_sub_node = None

      # Travel all sub nodes to find the best one
      for sub_node in node.get_children():

        # Ignore exploration for inference
        if is_exploration:
          C = 1 / math.sqrt(2.0)
          # C = 2
        else:
          C = 0.0

        # UCB = quality / times + C * sqrt(2 * ln(total_times) / times)
        left = sub_node.get_quality_value() / sub_node.get_visit_times()
        right = 2.0 * math.log(node.get_visit_times()) / sub_node.get_visit_times()
        score = left + C * sub_node.prob * math.sqrt(right)

        if score > best_score:
          best_sub_node = sub_node
          best_score = score

      return best_sub_node


    def backup(self, node, reward):
      """
      蒙特卡洛树搜索的Backpropagation阶段，输入前面获取需要expend的节点和新执行Action的reward，反馈给expend节点和上游所有节点并更新对应数据。
      """

      # Update util the root node
      while node != None:
        # Update the visit times
        node.visit_times_add_one()

        # Update the quality value
        node.quality_value_add_n(reward)

        # Change the node to the parent node
        node = node.parent


    def run(self):
      """
      实现蒙特卡洛树搜索算法，传入一个根节点，在有限的时间内根据之前已经探索过的树结构expand新节点和更新数据，然后返回只要exploitation最高的子节点。

      蒙特卡洛树搜索包含四个步骤，Selection、Expansion、Simulation、Backpropagation。
      前两步使用tree policy找到值得探索的节点。
      第三步使用default policy也就是在选中的节点上随机算法选一个子节点并计算reward。
      最后一步使用backup也就是把reward更新到所有经过的选中节点的节点上。

      进行预测时，只需要根据Q值选择exploitation最大的节点即可，找到下一个最优的节点。
      """
      node =  self.node
      computation_budget = 10

      # Run as much as possible under the computation budget
      for i in range(computation_budget):

        # 1. Find the best node to expand
        print("mcts训练到第{}次,node:".format(i, node.state))
        expand_node = self.tree_policy(node)
        # if(expand_node.state.state == 1):
        #   print("成功策略：")
        #   path = []
        #   state_list = []
        #   while expand_node.state.tac is not None:
        #       path.append(expand_node.state.tac)
        #       state_list.append(expand_node.state.state)
        #       expand_node = expand_node.parent
        #   path.reverse()
        #   state_list.append(node.state.state)
        #   state_list.reverse()
        #   print(path)
        #   print(state_list)
        #   return expand_node

        # 2. Random run to add node and get reward
        # reward = self.default_policy(expand_node)
        ############################################
        encodestate = encode_state(expand_node.state.state)
        input_value = torch.FloatTensor(np.array(encodestate).astype(np.float64))
        reward = float(self.value_model(input_value))
        #############################################
        
        # 如果到达叶子节点(证明成功)，终止循环，开始寻找其所用到的所有策略

        # 3. Update all passing nodes with reward
        self.backup(expand_node, reward)

      # N. Get the best next node
      # best_next_node = self.best_child(node, False)
      # return best_next_node
      
      return node

    def runmcts(self, root_name, assumptions, theorem):
        node =  self.node
        computation_budget = 10000

        # Run as much as possible under the computation budget
        for i in range(computation_budget):

          # 1. Find the best node to expand
          expand_node = self.tree_policy(node)
          if(expand_node.state.state == 1):
            print("成功策略：")
            path = []
            state_list = []
            while expand_node.state.tac is not None:
                path.append(expand_node.state.tac)
                state_list.append(expand_node.state.state)
                expand_node = expand_node.parent
            path.reverse()
            state_list.append(node.state.state)
            state_list.reverse()
            print(path)
            print(state_list)
            return expand_node

          # 2. Random run to add node and get reward
          # reward = self.default_policy(expand_node)
          ############################################
          encodestate = encode_state(expand_node.state.state)
          input_value = torch.FloatTensor(np.array(encodestate).astype(np.float64))
          reward = float(self.value_model(input_value))
          #############################################
          
          # 如果到达叶子节点(证明成功)，终止循环，开始寻找其所用到的所有策略

          # 3. Update all passing nodes with reward
          self.backup(expand_node, reward)

        # N. Get the best next node
        # best_next_node = self.best_child(node, False)
        # return best_next_node
        
        return 


def main():
  # Create the initialized state and initialized node
  init_state = State(state)
  node = Node()
  node.set_state(init_state)
  current_node = node
  mcts = MCTS(current_node)
  current_node = mcts.run()
  print("搜索完成")

# if __name__ == "__main__":
#   main()