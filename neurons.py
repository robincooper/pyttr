import numpy as np
from itertools import zip_longest
from tabulate import tabulate
from records import Rec
from utils import gensym

#######################

# Classes

#######################


class Neuron(object):
    def __init__(self,name=None,n=1):
        if name is None:
            self.name = gensym('neuron')
        else:
            self.name = name
        self.network = False
        self.synapses = []
        self.state = Rec({'dendrites' : np.array([0]*n),
                          'body' : {'w' : np.array([1]*n),
                                    'theta' : 1,
                                    'f' : AndFun},
                          'axon' : 0  
                          })
    def update(self,force=None):
        val = self.state.body.f(self.state.dendrites,
                                self.state.body.w,
                                self.state.body.theta)
        if force:
           self.state.axon = val
           for s in self.synapses:
               s.update()
        else:
            if not val == self.state.axon:
                self.state.axon = val
                for s in self.synapses:
                    s.update()
    def mark_update(self):
        if self.network:
            self.network.to_update.append(self)
    def excite(self,time='tick',array=None):
        if array is None:
            array = np.array([1])
        if len(array) == len(self.state.dendrites):
            self.state.dendrites = array
            self.update()
        netw = self.network
        if time == 'tick' and isinstance(netw,Network) and netw.ntracing():
            netw.ntrace()
    def inhibit(self,time='tick'):
        self.excite(time,np.array([0]*len(self.state.dendrites)))
    def fire(self,time='tick'):
        self.excite(time,np.array([self.state.body.theta]*len(self.state.dendrites)))
    def inactive(self):
        if self.state.axon == 0:
            return True
        else:
            return False
# The assumption is that exciting all dendrites with the threshold theta will
# cause the neuron to fire (i.e. state.axon is set to 1).  If not all neurons
# work like this then we need to redefine this.  Possibly by storing a firing
# condition on the neuron.  Similary with inhibit we are assuming that setting
# the state of all dendrites to 0 will cause the neuron not to fire
# (i.e. state.axon is set to 0).
    def spike(self,time='tick'):
        self.fire(time)
        self.inhibit()
        

class AndNeuron(Neuron):
    def __init__(self,n=2):
        self.synapses = []
        self.state = Rec({'dendrites' : np.array([0]*n),
                          'body' : {'w' : np.array([1]*n),
                                    'theta' : 1,
                                    'f' : AndFun},
                          'axon' : 0  
                          })

class OrNeuron(Neuron):
    def __init__(self,n=2):
        self.synapses = []
        self.state = Rec({'dendrites' : np.array([0]*n),
                          'body' : {'w' : np.array([1]*n),
                                    'theta' : 1,
                                    'f' : OrFun},
                          'axon' : 0  
                          })
class SwitchNeuron(Neuron):
    def __init__(self,name=None,n=2):
        if name is None:
            self.name = gensym('switchneuron')
        else:
            self.name = name
        self.network = False
        self.synapses = []
        self.state = Rec({'dendrites' : np.array([0]*n),
                          'body' : {'w' : np.array([1]*n),
                                    'theta' : 1,
                                    'f' : SwitchFun},
                          'axon' : 0  
                          })
    def fire(self,time='tick'):
        self.excite(time,np.array([self.state.body.theta,self.state.body.theta-.1]))

class DelayNeuron(Neuron):
    def __init__(self,delay=1,name='Delay',n=1):
        Neuron.__init__(self,name,n)
        self.delay = delay
        self.remaining_delay = delay
    def update(self,force=None):
        if self.remaining_delay and self.inactive():
            self.remaining_delay = self.remaining_delay-1
            self.mark_update()
        else:
            Neuron.update(self,force)
            self.remaining_delay = self.delay

# class HybridDelayNeuron(DelayNeuron):
#     def __init__(self,delay=1,name='Delay',n=1):
#         Neuron.__init__(self,name,n)
#         self.delay = delay
#         self.remaining_delay = delay
#         self.memory = None
#     def update(self):
#         val = self.state.body.f(self.state.dendrites,
#                                 self.state.body.w,
#                                 self.state.body.theta)
#         if not self.memory:
#             self.memory = val
#         if self.remaining_delay:
#             self.remaining_delay = self.remaining_delay-1
#             self.mark_update()
#         else:
#             self.state.axon = self.memory
#             self.memory = self.state.body.f(self.state.dendrites,
#                                 self.state.body.w,
#                                 self.state.body.theta)
#             self.remaining_delay = self.delay
#             for s in self.synapses:
#                 s.update()
            
            


class Synapse(object):
    def __init__(self,n1,n2,dend_num=0):
        self.from_neuron = n1
        self.to_neuron = Rec({'neuron' : n2,
                              'dend_num' : dend_num})
        self.state = Rec({'axon_mem' : [self.from_neuron.state.axon],
                          'w' : 1,
                          'f' : OneFun})
        self.from_neuron.synapses.append(self)
    def update(self):
        self.state.axon_mem.append(self.from_neuron.state.axon)
        val = self.state.f(self.state.axon_mem, self.state.w)
        if not val == 0:
            self.to_neuron.neuron.state.dendrites[self.to_neuron.dend_num] = val
            self.state.axon_mem = []
            self.to_neuron.neuron.mark_update()

class InhibitorySynapse(Synapse):
    def __init__(self,n1,n2,dend_num=0):
        Synapse.__init__(self,n1,n2,dend_num=0)
        self.state.w = -1

# class HybridSynapse(Synapse):
#     def update(self):
#         self.state.axon_mem.append(self.from_neuron.state.axon)
#         val = self.state.f(self.state.axon_mem, self.state.w)
#         if not self.to_neuron.neuron.state.dendrites[self.to_neuron.dend_num] == val:
#             self.to_neuron.neuron.state.dendrites[self.to_neuron.dend_num] = val
#             self.state.axon_mem = []
#             self.to_neuron.neuron.mark_update()

class Network(object):
    def __init__(self,neurons=np.array([])):
        self.name = gensym('network')
        self.neurons = neurons
        self.history = False
        self.to_update = []
    def add_neuron(self,name=None,den=1):
        neur = Neuron(name,n=den)
        neur.network = self
        self.neurons = np.concatenate((self.neurons,
                                       np.array([neur])))
        if not self.history is False:
           self.history = np.array([list(r)+[2] for r in self.history])
        return neur
    def add_switch_neuron(self,name=None):
        neur = SwitchNeuron(name)
        neur.network = self
        self.neurons = np.concatenate((self.neurons,
                                       np.array([neur])))
        if not self.history is False:
           self.history = np.array([list(r)+[2] for r in self.history])
        return neur
    def add_delay_neuron(self,delay=1,name='Delay'):
        n = DelayNeuron(delay,name)
        n.network = self
        self.neurons = np.concatenate((self.neurons,
                                       np.array([n])))
        if not self.history is False:
           self.history = np.array([[list(r)+[2]] for r in self.history])
        return n
    def add_hybrid_delay_neuron(self,delay=1,name='Delay'):
        n = HybridDelayNeuron(delay,name)
        n.network = self
        self.neurons = np.concatenate((self.neurons,
                                       np.array([n])))
        if not self.history is False:
           self.history = np.array([[list(r)+[2]] for r in self.history])
        return n
    def run(self,force=None):
        update_list = self.to_update
        self.to_update = []
        if update_list:
            for i in update_list:
                i.update(force)
            if self.ntracing():
                self.ntrace()
            self.run(force)
    def excite(self,neurons=None,arrays=None):
        if neurons is None:
            neurons = range(len(self.neurons))
        if arrays is None:
            arrays = [np.array([1])]*len(neurons)
        for i,ar in zip(neurons,arrays):
            self.neurons[i].excite('notick',ar)
        if self.ntracing():
            self.ntrace()
    def inhibit(self,time='tick',neurons=None):
        if neurons is None:
            neurons = range(len(self.neurons))
        for i in neurons:
            n = self.neurons[i]
            n.excite('notick',np.array([0]*len(n.state.dendrites)))
        if self.ntracing() and time == 'tick':
            self.ntrace()
    def fire(self,neurons=None):
        if neurons is None:
            neurons = range(len(self.neurons))
        for i in neurons:
            self.neurons[i].fire('notick')
        if self.ntracing():
            self.ntrace()
    def realize_apat(self,apat):
        if not apat.empty():
            for i,j in zip(apat.neurons,apat.vals):
                for n,v in zip(i,j):
                    if v == 1:
                        self.neurons[n].fire('notick')
                    elif v == 0:
                        self.neurons[n].inhibit('notick')
                    else:
                        print('Non-binary value in history pattern')
                        None
                if self.ntracing():
                    self.ntrace()
    def inhibit_apat(self,apat):
        self.realize_apat(ActivityPattern(apat.neurons,apat.vals*0))
    def memorize_apat(self,apat,name=gensym('mem')):
        mem_neuron = self.add_neuron(name)
        delay_neurons = []
        for i in range(len(apat.neurons)):
            #if i>0:
            delay_neurons.append(self.add_delay_neuron(i))
        #mem_neuron = delay_neurons[0]
        #mem_neuron.name = name
        #mem_neuron.delay = 1
        for n in delay_neurons:
            Synapse(mem_neuron,n)
        for i,j,k in zip(apat.neurons,apat.vals,delay_neurons):  #[mem_neuron]+
            for n,v in zip(i,j):
                if v == 1:
                    Synapse(k,self.neurons[n])
                elif v == 0:
                    InhibitorySynapse(k,self.neurons[n])
        InhibitorySynapse(delay_neurons[-1],mem_neuron)
        # for n in delay_neurons[1:]:
        #     n.delay = n.delay-1
        for n in delay_neurons:
            InhibitorySynapse(delay_neurons[-1],n)
        return mem_neuron
    def memorize_type(self,Tn,name=gensym('mem')):
        return self.memorize_apat(Tn.getapat(self).compact(),name)
    def memorize_judgmnt(self,Tn,an,name=gensym('judgemem')):
        return self.memorize_apat(Tn.judgmnt_type_n(an).getapat(self).compact(),
                                  name)
    def match_apat(self,apat,h=None):
        if h is None:
            h = self.history
        if isinstance(h,bool):
            print('Tracing not turned on for '+self.name)
            return None
        elif len(apat.neurons) == 0:
            return True
        elif len(apat.neurons)>len(h):
            return False
        elif all(h[0][np.asarray(apat.neurons[0], dtype='int64')] ==
                 np.asarray(apat.vals[0], dtype='int64')):
            return self.match_apat(ActivityPattern(list(apat.neurons[1:]),list(apat.vals[1:])),h[1:])
        else:
            return self.match_apat(apat,h[1:])
    def dump(self):
        return np.array([n.state.axon for n in self.neurons])
    def ntrace(self):
        if isinstance(self.history,bool):
            self.history = np.array([self.dump()])
        else:
            new = self.dump()
            if not all(self.history[-1] == new):
                self.history = np.row_stack((self.history,new))
    def nontrace(self):
        self.history = False
    def ntracing(self):
        return isinstance(self.history,np.ndarray)
    def display_history(self):
        l = np.row_stack((np.array([n.name for n in self.neurons]),
                            self.history)).transpose()
        l[l=='2'] = '*'
        print(tabulate(l))
                
        # print(
        #     tabulate(
        #         np.row_stack((np.array([n.name for n in self.neurons]),
        #                     self.history))
        #         .transpose()
        #         )
        #         )


class ActivityPattern(object):
    """First (indices) argument is a list of lists of array positions to be affected.  Or '[]' for the empty activity pattern (no effect on the network).

    Second (vals) argument is a list of lists showing the values (0
    or 1) to be assigned to the axons of the neurons in the array
    positions of the indices argument. Default is 1 for each neuron
    mentioned in indices at each tick."""
    def __init__(self,indices,vals=None):
        self.neurons = np.array([np.array(i, dtype='int64') for i in indices],
                                dtype=object)
        if vals is None:
            self.vals = np.array([np.array([1]*len(self.neurons[i]),
                                           dtype='int64')
                                  for i in range(len(self.neurons))],
                                 dtype=object)
        else:
            self.vals = np.array([np.array(i, dtype='int64') for i in vals],
                                 dtype=object)
    def empty(self):
        return list(self.neurons)==[]
    def compact(self):
        new_neurons = []
        new_vals = []
        def compact_line(ns,vs):
            for i in ns:
                count = ns.count(i)
                if count>1:
                    for j in range(count-1):
                        index = ns.index(i)
                        ns.pop(index)
                        vs.pop(index)
            return (ns,vs)
        for i,j in zip(self.neurons,self.vals):
            new_line = compact_line(list(i),list(j))
            if new_neurons == []:
                new_neurons = [new_line[0]]
                new_vals = [new_line[1]]
            else:
                to_delete = []
                for k in new_line[0]:
                    if [l for l in new_neurons if k in l]:
                        line_index = max(index for index,neurons in enumerate(new_neurons) if k in neurons)
                        k_index = new_line[0].index(k)
                        if new_line[1][k_index] == new_vals[line_index][new_neurons[line_index].index(k)]:
                            to_delete.append(k_index)
                new_line = (list(np.delete(new_line[0],to_delete)),list(np.delete(new_line[1],to_delete)))
                if new_line[0]:
                    new_neurons.append(new_line[0])
                    new_vals.append(new_line[1])
        return ActivityPattern(new_neurons,new_vals)
    def merge(self,apat):
        earr = np.array([],'int64')
        new_neurons = [np.concatenate((i,j))
                       for i,j in zip_longest(self.neurons,apat.neurons,fillvalue=earr)]
        new_vals = [np.concatenate((i,j))
                    for i,j in zip_longest(self.vals,apat.vals,fillvalue=earr)]
        return ActivityPattern(new_neurons,new_vals)
    def concat(self,apat):
        new_neurons = list(self.neurons)+list(apat.neurons)
        new_vals = list(self.vals)+list(apat.vals)
        return ActivityPattern(new_neurons,new_vals)
    def subapat_of(self,apat):
        if len(self.neurons) > len(apat.neurons):
            return False
        elif len(self.neurons) == 0:
            return True
        elif all(i in [x for x in zip(apat.neurons[0],apat.vals[0])]
                 for i in [x for x in zip(self.neurons[0],self.vals[0])]):
            return ActivityPattern(self.neurons[1:],
                                   self.vals[1:]).subapat_of(
                                       ActivityPattern(apat.neurons[1:],
                                                       apat.vals[1:]))
        else:
            return self.subapat_of(ActivityPattern(apat.neurons[1:],apat.vals[1:]))
    def show(self,network):
        l = [zip(i,j) for i,j in zip(self.neurons,self.vals)]
        return [[(x,network.neurons[x].name,y) for x,y in l[i]] for i in range(len(l))]
        

def merge_apat_list(l):
    if l == []:
        return ActivityPattern([])
    else:
        res = l[0]
        for i in l[1:]:
            res = res.merge(i)
        return res
        #return l[0].merge(merge_apat_list([l[1:]]))
    
class GensymNeuronTable(object):
    def __init__(self):
        self.table = {}
    def add_gensym_store(self,label):
        self.table[label] = {}
    def add_gensym_neuron(self,label,network):
        network.add_neuron(label)
        if label not in self.table:
            self.add_gensym_store(label)
        if network.name in self.table[label]:
            self.table[label][network.name].append(len(network.neurons)-1)
        else:
            self.table[label][network.name] = [len(network.neurons)-1]
    def index(self,label,network,assgn):
        # res = next(x for x in iter(self.table[label][network.name])
        #             if x not in assgn['in_use'])
        # assgn['in_use'].append(res)
        # return res
        if label in self.table and network.name in self.table[label]:
            l = [x for x in self.table[label][network.name]
                 if x not in assgn['in_use']] 
            #print(l)
            #print(network.dump())
            if l:
                res = next(iter(l))
                assgn['in_use'].append(res)
                #print(assgn['in_use'])
                return res
            else:
                self.add_gensym_neuron(label,network)
                return self.index(label,network,assgn)
        else:
          self.add_gensym_neuron(label,network)
          return self.index(label,network,assgn)  
                 
    def add_function_level(self,network):
        self.add_gensym_neuron('lambda',network)
        self.add_gensym_neuron('dom',network)
        self.add_gensym_neuron('var',network)
        self.add_gensym_neuron('rng',network)
    def add_function_levels(self,network,n):
        for i in range(n):
            self.add_function_level(network)
    def num_function_levels(self,network):
        return len(self.table['lambda'][network.name])
    def add_ptype_level(self,num_args,network):
        self.add_gensym_neuron('ptype'+str(num_args),network)
        self.add_gensym_neuron('rel',network)
        for i in range(num_args):
            self.add_gensym_neuron('arg'+str(i),network)
    def add_ptype_levels(self,num_args,network,n):
        for i in range(n):
            self.add_ptype_level(num_args,network)
    def num_ptype_levels(self,num_args,network):
        return len(self.table['ptype'+str(num_args)][network.name])
    def add_record_level(self,network):
        self.add_gensym_neuron('rec',network)
        #self.add_gensym_neuron('rectype',network)
    def add_record_levels(self,network,n):
        for i in range(n):
            self.add_record_level(network)



    

#######################

# Functions

#######################

# Functions for neuron bodies

def AndFun(dendrites,w,theta):
    if all(dendrites * w >= theta):
        return 1
    else:
        return 0

def OrFun(dendrites,w,theta):
    if any(dendrites * w >= theta):
        return 1
    else:
        return 0

def SwitchFun(dendrites,w,theta):
    if dendrites[0] * w[0] >= theta and dendrites[1]*w[1] < theta:
        return 1
    else:
        return 0


# Functions for synapses

def OneFun(l,w):
    if 1 in l:
        return w
    else:
        return 0

# def HybridOneFun(l,w):
#     if l[0] is 1:
#         return w
#     else:
#         return 0
