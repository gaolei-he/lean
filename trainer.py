import os
import numpy as np
from random import shuffle

import torch
import torch.optim as optim

from mcts import MCTS
from mcts import State

from transformers import AutoTokenizer, AutoModelForSeq2SeqLM

feature_size = 70

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
    
class Trainer:

    def __init__(self, policy_model, value_model, args):
        self.policy_model = policy_model
        self.value_model = value_model
        self.args = args
        self.mcts = None
        # self.mcts = MCTS(node, self.policy_model, self.value_model, self.args)


    def exceute_episode(self, root): # 返回当前搜索树大步路径上 所有 点的 概率、奖励、状态、策略 作为训练样本
        # print("开始采样")
        policy_examples = []
        value_examples = []
        # state = self.game.get_init_board()
        node = root
        state = node.state

        while True:  #循环一次是往下走一个节点，探索大步节点路径，直到证明结束（成功或失败），每一次选择孩子节点中价值最高的策略，并计算其选择概率，再将其状态和策略全部放入样本列表
            # canonical_board = self.game.get_canonical_board(state, current_player)
            max_times = 0
            max_i = 0
            finish = 0
            action_probs = [0 for _ in range(self.args['TACRIC_NUMBER'])]
            for index, children_node in enumerate(node.children):
                action_probs[index] = children_node.visit_times  
                if(action_probs[index] > max_times): # 找到当前节点中概率最大(访问次数最多)的子节点
                    max_times = action_probs[index]
                    max_i = index
            # print("节点")
            # print(action_probs)
            action_probs = action_probs / np.sum(action_probs)  #计算每个节点的概率值

            encodestate = encode_state(state.state)
            for index, children_node in enumerate(node.children):  #记录每个大步节点的所有策略的概率，放入train_examples
                encodetactic = encode_tactic(children_node.state.tac)
                input_policy = encodestate + encodetactic
                policy_examples.append((input_policy, action_probs[index]))
            
            try:
                node = node.children[max_i]
                state = node.state
                encodestate = encode_state(state.state)
                reward = state.compute_reward()  #当前节点的价值
                reward0 = reward
                if(reward is None):
                    reward0 = 0
                value_examples.append((encodestate, reward0)) #state为已完成或者失败时，reward直接为1or0
            except:
                finish == 1
                
            if (reward is not None or finish == 1):
                policy = []
                value = []
                for hist_input, hist_action_probs in policy_examples:
                    policy.append((hist_input, hist_action_probs))

                for hist_state, hist_reward in value_examples:
                    value.append((hist_state, hist_reward))

                # print("状态样本为：")
                # print(hist_state)
                # print("概率样本为：")
                # print(hist_action_probs)
                return policy, value


    def learn(self, node): 
        # print("训练开始啦")
        for i in range(1, self.args['numIters'] + 1):  # 每次迭代训练一个证明目标（即一个根节点node）
            print("{}/{}".format(i, self.args['numIters']))
            policy_train_example = []
            value_train_example = []
            count = 0
            node_ = node
            for j in range (self.args['numEps']): #对该证明目标训练的循环迭代次数，迭代一次，生成一棵搜索树，当迭代次数% b = 0， 则采样当前搜索树的大步节点，执行下列步骤 
                self.mcts = MCTS(node_, self.policy_model, self.value_model, self.args)
                # root = self.mcts.run()
                node_ = self.mcts.run()
                count += 1

                if(count % 2 == 0):
                # 如果迭代次数 % b = 0， 则采样，执行下列步骤 

                    policy_train_examples, value_train_examples = self.exceute_episode(node_)  # 都是列表，返回大步节点所构成的一条路径上所有样本数据。采样所有大步节点路径上的节点，每次循环返回一个训练样本，即一对（状态、策略）对 和 一个状态，及其相应的概率和价值
                    policy_train_example.extend(policy_train_examples)
                    value_train_example.extend(value_train_examples)

            shuffle(policy_train_example)
            shuffle(value_train_example)
            self.policy_train(policy_train_example)  # 每次训练样本：当前mcts树中，numEps/10条大步节点路径上所有节点
            self.value_train(value_train_example)
            # filename = self.args['checkpoint_path']
            # self.save_checkpoint(folder=".", filename=filename)  
        return

    def policy_train(self, policy_examples):
        # print("开始策略概率的训练")
        optimizer = optim.Adam(self.policy_model.parameters(), lr=5e-4)
        pi_losses = []

        for epoch in range(self.args['epochs']):
            self.policy_model.train()

            batch_idx = 0

            while batch_idx < int(len(policy_examples) / self.args['batch_size']):
                # sample_ids = np.random.randint(len(policy_examples), size=self.args['batch_size'])
                # input, pis = list(zip(*[policy_examples[i] for i in sample_ids]))
                # input = torch.FloatTensor(np.array(input).astype(np.float64))
                # target = torch.FloatTensor(np.array(pis))
                
                input, target = list(zip(*[(example[0], example[1]) for example in policy_examples]))
                input = torch.FloatTensor(np.array(input).astype(np.float64))
                target = torch.FloatTensor(np.array(target).astype(np.float64))

                # predict
                input = input.contiguous()
                target_pis = target.contiguous()
                
                
                out_pi = self.policy_model(input)
                l_pi = self.loss_pi(target_pis, out_pi)

                pi_losses.append(float(l_pi))

                optimizer.zero_grad()
                l_pi.backward()
                optimizer.step()

                batch_idx += 1

            print(pi_losses)
            print("Policy Loss", np.mean(pi_losses))
            # print("Examples:")
            # print(outpi[0].detach())
            # print(targetpis[0])


    def value_train(self, examples):
        # print("开始value的训练")
        optimizer = optim.Adam(self.value_model.parameters(), lr=5e-4)
        v_losses = []

        for epoch in range(self.args['epochs']):
            self.value_model.train()

            batch_idx = 0

            while batch_idx < int(len(examples) / 10):
                # sample_ids = np.random.randint(len(examples), size=self.args['batch_size'])
                # boards, vs = list(zip(*[examples[i] for i in sample_ids]))
                # boards = torch.FloatTensor(np.array(boards).astype(np.float64))
                # target_vs = torch.FloatTensor(np.array(vs).astype(np.float64))
                
                print("value训练开始了")
                input, target = list(zip(*[(example[0], example[1]) for example in examples]))
            
                input = torch.FloatTensor(np.array(input).astype(np.float64))
                target = torch.FloatTensor(np.array(target).astype(np.float64))

                # predict
                boards = input.contiguous()
                target_vs = target.contiguous()
               
                # compute output
                out_v = self.value_model(boards)
                l_v = self.loss_pi(target_vs, out_v)

                v_losses.append(float(l_v))

                optimizer.zero_grad()
                l_v.backward()
                optimizer.step()

                batch_idx += 1
            
            print(v_losses)
            print("Value Loss", np.mean(v_losses))
            # print("Examples:")
            # print(out_pi[0].detach())
            # print(target_pis[0])

    # def loss_pi(self, targets, outputs):
    #     loss = -(targets * torch.log(outputs)).sum(dim=1)
    #     return loss.mean()
    
    def loss_pi(self,targets, outputs):
        loss = torch.sum((targets - outputs) ** 2) / targets.size()[0]
        return loss

    def loss_v(self, targets, outputs):
        loss = torch.sum((targets-outputs.view(-1))**2)/targets.size()[0]
        return loss

    def save_checkpoint(self, folder, filename):
        if not os.path.exists(folder):
            os.mkdir(folder)

        filepath = os.path.join(folder, filename)
        torch.save({
            'state_dict': self.model.state_dict(),
        }, filepath)
