// height of the merge tree, layer 0 is for reorder input
parameter MERGE_TREE_HEIGHT=6;
// max number of nodes across all layers/height
parameter MERGE_TREE_MAX_NODES=14;
// number of nodes inside each layer, used to terminate generate for-loop
parameter int NODES_PER_LAYER [0:MERGE_TREE_HEIGHT-1] = '{ 14, 9, 6, 4, 2, 1 };
// actual merge plan [layer][node][plan], each plan is a two-integer tuple, meaning the idx of nodes to merge or queue in the previous layer. Equal idx means queue, else means merge.
// Height 0 is to shuffle the init channel width.
parameter int MERGE_PLAN [0:MERGE_TREE_HEIGHT-1] [0:MERGE_TREE_MAX_NODES-1] [0:1] = '{
'{'{12, 12}, '{13, 13}, '{8, 8}, '{5, 5}, '{2, 2}, '{7, 7}, '{9, 9}, '{11, 11}, '{3, 3}, '{10, 10}, '{4, 4}, '{6, 6}, '{1, 1}, '{0, 0}}, 
'{'{1, 2}, '{3, 4}, '{5, 5}, '{0, 0}, '{8, 9}, '{7, 7}, '{10, 11}, '{12, 13}, '{6, 6}, '{0, 0}, '{0, 0}, '{0, 0}, '{0, 0}, '{0, 0}}, 
'{'{1, 2}, '{0, 0}, '{3, 3}, '{5, 4}, '{6, 7}, '{8, 8}, '{0, 0}, '{0, 0}, '{0, 0}, '{0, 0}, '{0, 0}, '{0, 0}, '{0, 0}, '{0, 0}}, 
'{'{1, 0}, '{2, 2}, '{3, 4}, '{5, 5}, '{0, 0}, '{0, 0}, '{0, 0}, '{0, 0}, '{0, 0}, '{0, 0}, '{0, 0}, '{0, 0}, '{0, 0}, '{0, 0}}, 
'{'{1, 0}, '{3, 2}, '{0, 0}, '{0, 0}, '{0, 0}, '{0, 0}, '{0, 0}, '{0, 0}, '{0, 0}, '{0, 0}, '{0, 0}, '{0, 0}, '{0, 0}, '{0, 0}}, 
'{'{0, 1}, '{0, 0}, '{0, 0}, '{0, 0}, '{0, 0}, '{0, 0}, '{0, 0}, '{0, 0}, '{0, 0}, '{0, 0}, '{0, 0}, '{0, 0}, '{0, 0}, '{0, 0}}
};
// a shortcut to the shuffling plan (MERGE_PLAN[0])
parameter int SHUFFLE_PLAN [0:MERGE_TREE_MAX_NODES-1] [0:1] = MERGE_PLAN[0];
