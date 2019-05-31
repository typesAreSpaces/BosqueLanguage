//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRBasicBlock } from "../compiler/mir_ops";

export class QueueBlock {
    items: MIRBasicBlock[] = [];
    numberOfElements = 0;
    constructor() {
    }
    enqueue(x: MIRBasicBlock): void {
        if (this.items.length === 0) {
            this.items.push(x);
        }
        if (this.items.length == this.numberOfElements) {
            let newTable: MIRBasicBlock[] = [];
            newTable.length = 2 * this.items.length;
            for (var i in this.items) {
                newTable[i] = this.items[i];
            }
            this.items = newTable;
        }
        this.items[this.numberOfElements] = x;
        this.numberOfElements++;
    }
    dequeue(): MIRBasicBlock {
        if (this.items.length === 0) {
            throw new Error("No items to dequeue");
        }
        else {
            this.numberOfElements--;
            let result = this.items[this.numberOfElements];
            if (this.numberOfElements === 0) {
                this.items = [];
            }
            else {
                if (this.items.length > 2 * this.numberOfElements) {
                    let newTable: MIRBasicBlock[] = [];
                    newTable.length = this.items.length / 2;
                    var i = 0;
                    while (i < this.numberOfElements) {
                        newTable[i] = this.items[i];
                        i++;
                    }
                    this.items = newTable;
                }
            }
            return result;
        }
    }
    empty(): boolean {
        return this.numberOfElements === 0;
    }
}

