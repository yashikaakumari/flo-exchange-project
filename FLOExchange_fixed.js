'use strict';

(function (EXPORTS) { //floExchangeAPI v1.2.2 (Final Fix)

    // ====================================================================================
    // FIX 1: ENVIRONMENT & DEPENDENCY STUBS
    // These stubs prevent the script from crashing if loaded in an environment where its
    // dependencies (other scripts in FLOPay) haven't loaded yet. They provide safe
    // default values and placeholder functions.
    // ====================================================================================

    const floGlobals = (typeof globalThis.floGlobals !== 'undefined') ? globalThis.floGlobals : {};
    const floCrypto = (typeof globalThis.floCrypto !== 'undefined') ? globalThis.floCrypto : {
        getFloID: () => null,
        getPubKeyHex: () => null,
        signData: () => null,
        validateAddr: () => false,
        verifyPrivKey: () => false
    };
    const floBlockchainAPI = (typeof globalThis.floBlockchainAPI !== 'undefined') ? globalThis.floBlockchainAPI : {
        readData: () => Promise.reject("floBlockchainAPI not loaded"),
        sendTx: () => Promise.reject("floBlockchainAPI not loaded")
    };
    const floTokenAPI = (typeof globalThis.floTokenAPI !== 'undefined') ? globalThis.floTokenAPI : {
        sendToken: () => Promise.reject("floTokenAPI not loaded")
    };
    const btcOperator = (typeof globalThis.btcOperator !== 'undefined') ? globalThis.btcOperator : {
        convert: { legacy2bech: () => null },
        createSignedTx: () => Promise.reject("btcOperator not loaded"),
        transactionID: () => null,
        sendTx: () => Promise.reject("btcOperator not loaded")
    };
    const bitjs = (typeof globalThis.bitjs !== 'undefined') ? globalThis.bitjs : { Base58: { decode: () => [0,0,0,0,0] }};
    const Crypto = (typeof globalThis.Crypto !== 'undefined') ? globalThis.Crypto : { 
        util: { bytesToHex: () => "" },
        AES: { encrypt: () => "", decrypt: () => "" }
    };
    const BigInteger = (typeof globalThis.BigInteger !== 'undefined') ? globalThis.BigInteger : function() { return { toByteArrayUnsigned: () => [] }};

    // Stubs for UI functions that are defined elsewhere in FLOPay
    const notify = (typeof globalThis.notify !== 'undefined') ? globalThis.notify : (message, type) => console.log(`[${type || 'info'}] ${message}`);
    const getPromptInput = (typeof globalThis.getPromptInput !== 'undefined') ? globalThis.getPromptInput : () => Promise.reject("UI function getPromptInput not available");

    // Polyfill for browser-specific APIs to prevent crashes in other environments
    const g_window = (typeof window !== 'undefined') ? window : { crypto: { getRandomValues: (arr) => arr } };
    const g_localStorage = (typeof localStorage !== 'undefined') ? localStorage : { getItem: () => null, setItem: () => {}, removeItem: () => {} };
    const g_location = (typeof location !== 'undefined') ? location : { reload: () => {} };


    const exchangeAPI = EXPORTS;

    const DEFAULT = {
        marketID: floGlobals.marketID || "FMxYC7gYZhouzqtHZukGnPiQ8nvG4CMzXM",
        marketApp: "exchange"
    }

    function BuildKBucket(options = {}) {
        this.localNodeId = options.localNodeId || g_window.crypto.getRandomValues(new Uint8Array(20))
        this.numberOfNodesPerKBucket = options.numberOfNodesPerKBucket || 20
        this.numberOfNodesToPing = options.numberOfNodesToPing || 3
        this.distance = options.distance || this.distance
        this.arbiter = options.arbiter || this.arbiter
        this.metadata = Object.assign({}, options.metadata)

        this.createNode = function () {
            return {
                contacts: [],
                dontSplit: false,
                left: null,
                right: null
            }
        }

        this.ensureInt8 = function (name, val) {
            if (!(val instanceof Uint8Array)) {
                throw new TypeError(name + ' is not a Uint8Array')
            }
        }

        this.arrayEquals = function (array1, array2) {
            if (array1 === array2) {
                return true
            }
            if (array1.length !== array2.length) {
                return false
            }
            for (let i = 0, length = array1.length; i < length; ++i) {
                if (array1[i] !== array2[i]) {
                    return false
                }
            }
            return true
        }

        this.ensureInt8('option.localNodeId as parameter 1', this.localNodeId)
        this.root = this.createNode()

        this.arbiter = function (incumbent, candidate) {
            return incumbent.vectorClock > candidate.vectorClock ? incumbent : candidate
        }

        this.distance = function (firstId, secondId) {
            let distance = 0
            let i = 0
            const min = Math.min(firstId.length, secondId.length)
            const max = Math.max(firstId.length, secondId.length)
            for (; i < min; ++i) {
                distance = distance * 256 + (firstId[i] ^ secondId[i])
            }
            for (; i < max; ++i) distance = distance * 256 + 255
            return distance
        }

        this.add = function (contact) {
            this.ensureInt8('contact.id', (contact || {}).id)
            let bitIndex = 0
            let node = this.root
            while (node.contacts === null) {
                node = this._determineNode(node, contact.id, bitIndex++)
            }
            const index = this._indexOf(node, contact.id)
            if (index >= 0) {
                this._update(node, index, contact)
                return this
            }
            if (node.contacts.length < this.numberOfNodesPerKBucket) {
                node.contacts.push(contact)
                return this
            }
            if (node.dontSplit) {
                return this
            }
            this._split(node, bitIndex)
            return this.add(contact)
        }

        this.closest = function (id, n = Infinity) {
            this.ensureInt8('id', id)
            if ((!Number.isInteger(n) && n !== Infinity) || n <= 0) {
                throw new TypeError('n is not positive number')
            }
            let contacts = []
            for (let nodes = [this.root], bitIndex = 0; nodes.length > 0 && contacts.length < n;) {
                const node = nodes.pop()
                if (node.contacts === null) {
                    const detNode = this._determineNode(node, id, bitIndex++)
                    nodes.push(node.left === detNode ? node.right : node.left)
                    nodes.push(detNode)
                } else {
                    contacts = contacts.concat(node.contacts)
                }
            }
            return contacts
                .map(a => [this.distance(a.id, id), a])
                .sort((a, b) => a[0] - b[0])
                .slice(0, n)
                .map(a => a[1])
        }

        this.count = function () {
            let count = 0
            for (const nodes = [this.root]; nodes.length > 0;) {
                const node = nodes.pop()
                if (node.contacts === null) nodes.push(node.right, node.left)
                else count += node.contacts.length
            }
            return count
        }

        this._determineNode = function (node, id, bitIndex) {
            const bytesDescribedByBitIndex = bitIndex >> 3
            const bitIndexWithinByte = bitIndex % 8
            if ((id.length <= bytesDescribedByBitIndex) && (bitIndexWithinByte !== 0)) {
                return node.left
            }
            const byteUnderConsideration = id[bytesDescribedByBitIndex]
            if (byteUnderConsideration & (1 << (7 - bitIndexWithinByte))) {
                return node.right
            }
            return node.left
        }

        this.get = function (id) {
            this.ensureInt8('id', id)
            let bitIndex = 0
            let node = this.root
            while (node.contacts === null) {
                node = this._determineNode(node, id, bitIndex++)
            }
            const index = this._indexOf(node, id)
            return index >= 0 ? node.contacts[index] : null
        }

        this._indexOf = function (node, id) {
            for (let i = 0; i < node.contacts.length; ++i) {
                if (this.arrayEquals(node.contacts[i].id, id)) return i
            }
            return -1
        }

        this.remove = function (id) {
            this.ensureInt8('the id as parameter 1', id)
            let bitIndex = 0
            let node = this.root
            while (node.contacts === null) {
                node = this._determineNode(node, id, bitIndex++)
            }
            const index = this._indexOf(node, id)
            if (index >= 0) {
                node.contacts.splice(index, 1)[0]
            }
            return this
        }

        this._split = function (node, bitIndex) {
            node.left = this.createNode()
            node.right = this.createNode()
            for (const contact of node.contacts) {
                this._determineNode(node, contact.id, bitIndex).contacts.push(contact)
            }
            node.contacts = null
            const detNode = this._determineNode(node, this.localNodeId, bitIndex)
            const otherNode = node.left === detNode ? node.right : node.left
            otherNode.dontSplit = true
        }

        this.toArray = function () {
            let result = []
            for (const nodes = [this.root]; nodes.length > 0;) {
                const node = nodes.pop()
                if (node.contacts === null) nodes.push(node.right, node.left)
                else result = result.concat(node.contacts)
            }
            return result
        }

        this._update = function (node, index, contact) {
            if (!this.arrayEquals(node.contacts[index].id, contact.id)) {
                throw new Error('wrong index for _update')
            }
            const incumbent = node.contacts[index]
            const selection = this.arbiter(incumbent, contact)
            if (selection === incumbent && incumbent !== contact) return
            node.contacts.splice(index, 1)
            node.contacts.push(selection)
        }
    }

    const K_Bucket = exchangeAPI.K_Bucket = function K_Bucket(masterID, backupList) {
        const decodeID = function (floID) {
            let k = bitjs.Base58.decode(floID);
            k.shift();
            k.splice(-4, 4);
            const decodedId = Crypto.util.bytesToHex(k);
            const nodeIdBigInt = new BigInteger(decodedId, 16);
            const nodeIdBytes = nodeIdBigInt.toByteArrayUnsigned();
            return new Uint8Array(nodeIdBytes);
        };
        const _KB = new BuildKBucket({
            localNodeId: decodeID(masterID)
        });
        backupList.forEach(id => _KB.add({
            id: decodeID(id),
            floID: id
        }));
        const orderedList = backupList.map(sn => [_KB.distance(decodeID(masterID), decodeID(sn)), sn])
            .sort((a, b) => a[0] - b[0])
            .map(a => a[1]);
        const self = this;

        Object.defineProperty(self, 'order', {
            get: () => Array.from(orderedList)
        });

        self.closestNode = function (id, N = 1) {
            let decodedId = decodeID(id);
            let n = N || orderedList.length;
            let cNodes = _KB.closest(decodedId, n)
                .map(k => k.floID);
            return (N === 1 ? cNodes[0] : cNodes);
        };

        self.isBefore = (source, target) => orderedList.indexOf(target) < orderedList.indexOf(source);
        self.isAfter = (source, target) => orderedList.indexOf(target) > orderedList.indexOf(source);
        self.isPrev = (source, target) => orderedList.indexOf(target) === orderedList.indexOf(source) - 1;
        self.isNext = (source, target) => orderedList.indexOf(target) === orderedList.indexOf(source) + 1;

        self.prevNode = function (id, N = 1) {
            let n = N || orderedList.length;
            if (!orderedList.includes(id))
                throw Error(`${id} is not in KB list`);
            let pNodes = orderedList.slice(0, orderedList.indexOf(id)).slice(-n);
            return (N === 1 ? pNodes[0] : pNodes);
        };

        self.nextNode = function (id, N = 1) {
            let n = N || orderedList.length;
            if (!orderedList.includes(id))
                throw Error(`${id} is not in KB list`);
            let nNodes = orderedList.slice(orderedList.indexOf(id) + 1).slice(0, n);
            return (N === 1 ? nNodes[0] : nNodes);
        };
    }

    var nodeList, nodeURL, nodeKBucket;
    var fetch_api_pos = 0;

    Object.defineProperties(exchangeAPI, {
        adminID: {
            get: () => DEFAULT.marketID
        },
        application: {
            get: () => DEFAULT.marketApp
        },
        nodeList: {
            get: () => {
                if (Array.isArray(nodeList))
                    return Array.from(nodeList);
                else
                    throw "Exchange API is not loaded";
            }
        }
    });

    // ====================================================================================
    // FIX 2 & 3: IMPROVED NETWORK LOGIC & CLEAN CONSOLE
    // This function now uses a stable loop instead of recursion. The `console.warn`
    // for offline nodes has been removed to prevent cluttering the console.
    // ====================================================================================
    async function fetch_api(api, options) {
        if (!nodeList || !nodeList.length) {
            return Promise.reject(ExchangeError(ExchangeError.NODES_OFFLINE_CODE, 'Node list is empty', errorCode.NODES_OFFLINE));
        }

        for (let i = 0; i < nodeList.length; i++) {
            let currentPos = (fetch_api_pos + i) % nodeList.length;
            let node = nodeList[currentPos];
            let url = "https://" + nodeURL[node];

            try {
                const response = await (options ? fetch(url + api, options) : fetch(url + api));
                fetch_api_pos = currentPos;
                return response;
            } catch (error) {
                // This is where the "is offline" warning used to be. It has been removed.
                if (i === nodeList.length - 1) {
                    return Promise.reject(ExchangeError(ExchangeError.NODES_OFFLINE_CODE, 'No Node online! Refresh the page or try again later', errorCode.NODES_OFFLINE));
                }
            }
        }
    }

    const errorCode = exchangeAPI.errorCode = {
        INCORRECT_SERVER: '000',
        INVALID_REQUEST_FORMAT: '001',
        ACCESS_DENIED: '002',
        INVALID_FLO_ID: '011',
        INVALID_LOGIN_CODE: '012',
        INVALID_PRIVATE_KEY: '013',
        INVALID_PUBLIC_KEY: '014',
        INVALID_SIGNATURE: '015',
        EXPIRED_SIGNATURE: '016',
        DUPLICATE_SIGNATURE: '017',
        SESSION_INVALID: '018',
        SESSION_EXPIRED: '019',
        INVALID_VALUE: '020',
        INVALID_TOKEN_NAME: '021',
        INVALID_NUMBER: '022',
        INVALID_TYPE: '023',
        INVALID_TX_ID: '024',
        INVALID_TAG: '025',
        MISSING_PARAMETER: '099',
        NOT_FOUND: '101',
        NOT_OWNER: '102',
        DUPLICATE_ENTRY: '103',
        INSUFFICIENT_BALANCE: '201',
        INSUFFICIENT_SELLCHIP: '203',
        GREATER_SELLCHIP_BASE: '204',
        INSUFFICIENT_PERIOD: '206',
        INSUFFICIENT_FUND: '207',
        NODES_OFFLINE: '404',
        INTERNAL_ERROR: '500'
    };

    const parseErrorCode = exchangeAPI.parseErrorCode = function (message) {
        let code = String(message || '').match(/^E\d{3}:/g);
        if (!code || !code.length)
            return null;
        else
            return code[0].substring(1, 4);
    }

    function ExchangeError(status, message, code = null) {
        if (parseErrorCode(message) === errorCode.INCORRECT_SERVER)
            g_location.reload();
        else if (this instanceof ExchangeError) {
            this.code = code || parseErrorCode(message);
            this.message = String(message || '').replace(/^E\d{3}:/g, '').trim();
            this.status = status;
        } else
            return new ExchangeError(status, message, code);
    }

    ExchangeError.BAD_REQUEST_CODE = 400;
    ExchangeError.BAD_RESPONSE_CODE = 500;
    ExchangeError.NODES_OFFLINE_CODE = 404;

    function responseParse(response, json_ = true) {
        return new Promise((resolve, reject) => {
            if (!response.ok)
                response.text()
                .then(result => reject(ExchangeError(response.status, result)))
                .catch(error => reject(ExchangeError(response.status, error)));
            else if (json_)
                response.json()
                .then(result => resolve(result))
                .catch(error => reject(ExchangeError(ExchangeError.BAD_RESPONSE_CODE, error)));
            else
                response.text()
                .then(result => resolve(result))
                .catch(error => reject(ExchangeError(ExchangeError.BAD_RESPONSE_CODE, error)));
        });
    }

    const processCode = exchangeAPI.processCode = {
        ASSET_TYPE_COIN: 0,
        ASSET_TYPE_TOKEN: 1,
        VAULT_MODE_DEPOSIT: 1,
        VAULT_MODE_WITHDRAW: 0,
        STATUS_PENDING: 0,
        STATUS_PROCESSING: 1,
        STATUS_CONFIRMATION: 90,
        STATUS_REJECTED: -1,
        STATUS_SUCCESS: 100,
        CONVERT_MODE_GET: 1,
        CONVERT_MODE_PUT: 0,
    }

    const serviceList = exchangeAPI.serviceList = {
        EXCHANGE: "exchange",
        CONVERT: "convert",
        BLOCKCHAIN_BOND: "blockchain-bond",
        BOBS_FUND: "bobs-fund"
    }

    const getSink = exchangeAPI.getSink = function (service = serviceList.EXCHANGE) {
        if (!(Object.values(serviceList).includes(service)))
            return Promise.reject(ExchangeError(ExchangeError.BAD_REQUEST_CODE, 'service required', errorCode.INVALID_VALUE));
        return fetch_api('/get-sink?service=' + service)
            .then(result => responseParse(result, false));
    }

    exchangeAPI.getAccount = function (floID, proxySecret) {
        let request = {
            floID: floID,
            timestamp: Date.now()
        };
        if (floCrypto.getFloID(proxySecret) === floID)
            request.pubKey = floCrypto.getPubKeyHex(proxySecret);
        request.sign = signRequest({
            type: "get_account",
            timestamp: request.timestamp
        }, proxySecret);
        return fetch_api('/account', {
            method: "POST",
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify(request)
        }).then(responseParse);
    }

    exchangeAPI.getBuyList = function (asset = null) {
        return fetch_api('/list-buyorders' + (asset ? "?asset=" + asset : "")).then(responseParse);
    }

    exchangeAPI.getSellList = function (asset = null) {
        return fetch_api('/list-sellorders' + (asset ? "?asset=" + asset : "")).then(responseParse);
    }

    exchangeAPI.getTradeList = function (asset = null) {
        return fetch_api('/list-trades' + (asset ? "?asset=" + asset : "")).then(responseParse);
    }

    exchangeAPI.getRates = function (asset = null) {
        return fetch_api('/get-rates' + (asset ? "?asset=" + asset : "")).then(responseParse);
    }

    exchangeAPI.getRateHistory = function (asset, duration = null) {
        return fetch_api('/rate-history?asset=' + asset + (duration ? '&duration=' + duration : "")).then(responseParse);
    }

    exchangeAPI.getBalance = function (floID = null, token = null) {
        if (!floID && !token)
            return Promise.reject(ExchangeError(ExchangeError.BAD_REQUEST_CODE, "Need atleast one argument", errorCode.MISSING_PARAMETER));
        let queryStr = (floID ? "floID=" + floID : "") +
            (floID && token ? "&" : "") +
            (token ? "token=" + token : "");
        return fetch_api('/get-balance?' + queryStr).then(responseParse);
    }

    exchangeAPI.getTx = function (txid) {
        if (!txid)
            return Promise.reject(ExchangeError(ExchangeError.BAD_REQUEST_CODE, 'txid required', errorCode.MISSING_PARAMETER));
        return fetch_api('/get-transaction?txid=' + txid).then(responseParse);
    }

    function signRequest(request, signKey) {
        if (typeof request !== "object")
            throw Error("Request is not an object");
        let req_str = Object.keys(request).sort().map(r => r + ":" + request[r]).join("|");
        return floCrypto.signData(req_str, signKey);
    }

    exchangeAPI.getLoginCode = function () {
        return fetch_api('/get-login-code').then(responseParse);
    }

    exchangeAPI.login = function (privKey, proxyKey, code, hash) {
        if (!code || !hash)
            return Promise.reject(ExchangeError(ExchangeError.BAD_REQUEST_CODE, "Login Code missing", errorCode.MISSING_PARAMETER));
        let request = {
            proxyKey: proxyKey,
            floID: floCrypto.getFloID(privKey),
            pubKey: floCrypto.getPubKeyHex(privKey),
            timestamp: Date.now(),
            code: code,
            hash: hash
        };
        if (!privKey || !request.floID)
            return Promise.reject(ExchangeError(ExchangeError.BAD_REQUEST_CODE, "Invalid Private key", errorCode.INVALID_PRIVATE_KEY));
        request.sign = signRequest({
            type: "login",
            random: code,
            proxyKey: proxyKey,
            timestamp: request.timestamp
        }, privKey);
        return fetch_api("/login", {
            method: "POST",
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify(request)
        }).then(r => responseParse(r, false));
    }

    exchangeAPI.logout = function (floID, proxySecret) {
        let request = {
            floID: floID,
            timestamp: Date.now()
        };
        if (floCrypto.getFloID(proxySecret) === floID)
            request.pubKey = floCrypto.getPubKeyHex(proxySecret);
        request.sign = signRequest({
            type: "logout",
            timestamp: request.timestamp
        }, proxySecret);
        return fetch_api("/logout", {
            method: "POST",
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify(request)
        }).then(r => responseParse(r, false));
    }

    exchangeAPI.buy = function (asset, quantity, max_price, floID, proxySecret) {
        if (typeof quantity !== "number" || quantity <= 0)
            return Promise.reject(ExchangeError(ExchangeError.BAD_REQUEST_CODE, `Invalid quantity (${quantity})`, errorCode.INVALID_NUMBER));
        if (typeof max_price !== "number" || max_price <= 0)
            return Promise.reject(ExchangeError(ExchangeError.BAD_REQUEST_CODE, `Invalid max_price (${max_price})`, errorCode.INVALID_NUMBER));
        let request = {
            floID: floID,
            asset: asset,
            quantity: quantity,
            max_price: max_price,
            timestamp: Date.now()
        };
        if (floCrypto.getFloID(proxySecret) === floID)
            request.pubKey = floCrypto.getPubKeyHex(proxySecret);
        request.sign = signRequest({
            type: "buy_order",
            asset: asset,
            quantity: quantity,
            max_price: max_price,
            timestamp: request.timestamp
        }, proxySecret);
        return fetch_api('/buy', {
            method: "POST",
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify(request)
        }).then(r => responseParse(r, false));
    }

    exchangeAPI.sell = function (asset, quantity, min_price, floID, proxySecret) {
        if (typeof quantity !== "number" || quantity <= 0)
            return Promise.reject(ExchangeError(ExchangeError.BAD_REQUEST_CODE, `Invalid quantity (${quantity})`, errorCode.INVALID_NUMBER));
        if (typeof min_price !== "number" || min_price <= 0)
            return Promise.reject(ExchangeError(ExchangeError.BAD_REQUEST_CODE, `Invalid min_price (${min_price})`, errorCode.INVALID_NUMBER));
        let request = {
            floID: floID,
            asset: asset,
            quantity: quantity,
            min_price: min_price,
            timestamp: Date.now()
        };
        if (floCrypto.getFloID(proxySecret) === floID)
            request.pubKey = floCrypto.getPubKeyHex(proxySecret);
        request.sign = signRequest({
            type: "sell_order",
            quantity: quantity,
            asset: asset,
            min_price: min_price,
            timestamp: request.timestamp
        }, proxySecret);
        return fetch_api('/sell', {
            method: "POST",
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify(request)
        }).then(r => responseParse(r, false));
    }

    exchangeAPI.cancelOrder = function (type, id, floID, proxySecret) {
        if (type !== "buy" && type !== "sell")
            return Promise.reject(ExchangeError(ExchangeError.BAD_REQUEST_CODE, `Invalid type (${type}): type should be sell (or) buy`, errorCode.INVALID_TYPE));
        let request = {
            floID: floID,
            orderType: type,
            orderID: id,
            timestamp: Date.now()
        };
        if (floCrypto.getFloID(proxySecret) === floID)
            request.pubKey = floCrypto.getPubKeyHex(proxySecret);
        request.sign = signRequest({
            type: "cancel_order",
            order: type,
            id: id,
            timestamp: request.timestamp
        }, proxySecret);
        return fetch_api('/cancel', {
            method: "POST",
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify(request)
        }).then(r => responseParse(r, false));
    }

    exchangeAPI.transferToken = function (receiver, token, floID, proxySecret) {
        if (typeof receiver !== 'object' || receiver === null)
            return Promise.reject(ExchangeError(ExchangeError.BAD_REQUEST_CODE, "Invalid receiver: parameter is not an object", errorCode.INVALID_FLO_ID));
        let invalidIDs = [],
            invalidAmt = [];
        for (let f in receiver) {
            if (!floCrypto.validateAddr(f))
                invalidIDs.push(f);
            else if (typeof receiver[f] !== "number" || receiver[f] <= 0)
                invalidAmt.push(receiver[f])
        }
        if (invalidIDs.length)
            return Promise.reject(ExchangeError(ExchangeError.BAD_REQUEST_CODE, `Invalid receiver (${invalidIDs})`, errorCode.INVALID_FLO_ID));
        if (invalidAmt.length)
            return Promise.reject(ExchangeError(ExchangeError.BAD_REQUEST_CODE, `Invalid amount (${invalidAmt})`, errorCode.INVALID_NUMBER));
        let request = {
            floID: floID,
            token: token,
            receiver: receiver,
            timestamp: Date.now()
        };
        if (floCrypto.getFloID(proxySecret) === floID)
            request.pubKey = floCrypto.getPubKeyHex(proxySecret);
        request.sign = signRequest({
            type: "transfer_token",
            receiver: JSON.stringify(receiver),
            token: token,
            timestamp: request.timestamp
        }, proxySecret);
        return fetch_api('/transfer-token', {
            method: "POST",
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify(request)
        }).then(r => responseParse(r, false));
    }

    exchangeAPI.depositFLO = function (quantity, floID, sinkID, privKey, proxySecret = null) {
        return new Promise((resolve, reject) => {
            if (typeof quantity !== "number" || quantity <= (floGlobals.fee || 0))
                return reject(ExchangeError(ExchangeError.BAD_REQUEST_CODE, `Invalid quantity (${quantity})`, errorCode.INVALID_NUMBER));
            if (!floCrypto.verifyPrivKey(privKey, floID))
                return reject(ExchangeError(ExchangeError.BAD_REQUEST_CODE, "Invalid Private Key", errorCode.INVALID_PRIVATE_KEY));
            
            floBlockchainAPI.sendTx(floID, sinkID, quantity, privKey, '(deposit in market)').then(txid => {
                let request = {
                    floID: floID,
                    txid: txid,
                    timestamp: Date.now()
                };
                if (!proxySecret)
                    request.pubKey = floCrypto.getPubKeyHex(privKey);
                request.sign = signRequest({
                    type: "deposit_flo",
                    txid: txid,
                    timestamp: request.timestamp
                }, proxySecret || privKey);
                fetch_api('/deposit-flo', {
                    method: "POST",
                    headers: { 'Content-Type': 'application/json' },
                    body: JSON.stringify(request)
                }).then(r => responseParse(r, false)).then(resolve).catch(reject);
            }).catch(reject);
        });
    }

    exchangeAPI.withdrawFLO = function (quantity, floID, proxySecret) {
        let request = {
            floID: floID,
            amount: quantity,
            timestamp: Date.now()
        };
        if (floCrypto.getFloID(proxySecret) === floID)
            request.pubKey = floCrypto.getPubKeyHex(proxySecret);
        request.sign = signRequest({
            type: "withdraw_flo",
            amount: quantity,
            timestamp: request.timestamp
        }, proxySecret);
        return fetch_api('/withdraw-flo', {
            method: "POST",
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify(request)
        }).then(r => responseParse(r, false));
    }

    exchangeAPI.depositToken = function (token, quantity, floID, sinkID, privKey, proxySecret = null) {
        return new Promise((resolve, reject) => {
            if (!floCrypto.verifyPrivKey(privKey, floID))
                return reject(ExchangeError(ExchangeError.BAD_REQUEST_CODE, "Invalid Private Key", errorCode.INVALID_PRIVATE_KEY));
            
            floTokenAPI.sendToken(privKey, quantity, sinkID, '(deposit in market)', token).then(txid => {
                let request = {
                    floID: floID,
                    txid: txid,
                    timestamp: Date.now()
                };
                if (!proxySecret)
                    request.pubKey = floCrypto.getPubKeyHex(privKey);
                request.sign = signRequest({
                    type: "deposit_token",
                    txid: txid,
                    timestamp: request.timestamp
                }, proxySecret || privKey);
                fetch_api('/deposit-token', {
                    method: "POST",
                    headers: { 'Content-Type': 'application/json' },
                    body: JSON.stringify(request)
                }).then(r => responseParse(r, false)).then(resolve).catch(reject);
            }).catch(reject);
        });
    }

    exchangeAPI.withdrawToken = function (token, quantity, floID, proxySecret) {
        let request = {
            floID: floID,
            token: token,
            amount: quantity,
            timestamp: Date.now()
        };
        if (floCrypto.getFloID(proxySecret) === floID)
            request.pubKey = floCrypto.getPubKeyHex(proxySecret);
        request.sign = signRequest({
            type: "withdraw_token",
            token: token,
            amount: quantity,
            timestamp: request.timestamp
        }, proxySecret);
        return fetch_api('/withdraw-token', {
            method: "POST",
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify(request)
        }).then(r => responseParse(r, false));
    }

    exchangeAPI.getUserTransacts = function (floID, proxySecret) {
        let request = {
            floID: floID,
            timestamp: Date.now()
        };
        if (floCrypto.getFloID(proxySecret) === floID)
            request.pubKey = floCrypto.getPubKeyHex(proxySecret);
        request.sign = signRequest({
            type: "get_transact",
            timestamp: request.timestamp
        }, proxySecret);
        return fetch_api('/get-transact', {
            method: "POST",
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify(request)
        }).then(responseParse);
    }

    exchangeAPI.addUserTag = function (tag_user, tag, floID, proxySecret) {
        let request = {
            floID: floID,
            user: tag_user,
            tag: tag,
            timestamp: Date.now()
        };
        if (floCrypto.getFloID(proxySecret) === floID)
            request.pubKey = floCrypto.getPubKeyHex(proxySecret);
        request.sign = signRequest({
            type: "add_tag",
            user: tag_user,
            tag: tag,
            timestamp: request.timestamp
        }, proxySecret);
        return fetch_api('/add-tag', {
            method: "POST",
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify(request)
        }).then(r => responseParse(r, false));
    }

    exchangeAPI.removeUserTag = function (tag_user, tag, floID, proxySecret) {
        let request = {
            floID: floID,
            user: tag_user,
            tag: tag,
            timestamp: Date.now()
        };
        if (floCrypto.getFloID(proxySecret) === floID)
            request.pubKey = floCrypto.getPubKeyHex(proxySecret);
        request.sign = signRequest({
            type: "remove_tag",
            user: tag_user,
            tag: tag,
            timestamp: request.timestamp
        }, proxySecret);
        return fetch_api('/remove-tag', {
            method: "POST",
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify(request)
        }).then(r => responseParse(r, false));
    }

    exchangeAPI.addDistributor = function (distributor, asset, floID, proxySecret) {
        let request = {
            floID: floID,
            distributor: distributor,
            asset: asset,
            timestamp: Date.now()
        };
        if (floCrypto.getFloID(proxySecret) === floID)
            request.pubKey = floCrypto.getPubKeyHex(proxySecret);
        request.sign = signRequest({
            type: "add_distributor",
            distributor: distributor,
            asset: asset,
            timestamp: request.timestamp
        }, proxySecret);
        return fetch_api('/add-distributor', {
            method: "POST",
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify(request)
        }).then(r => responseParse(r, false));
    }

    exchangeAPI.removeDistributor = function (distributor, asset, floID, proxySecret) {
        let request = {
            floID: floID,
            distributor: distributor,
            asset: asset,
            timestamp: Date.now()
        };
        if (floCrypto.getFloID(proxySecret) === floID)
            request.pubKey = floCrypto.getPubKeyHex(proxySecret);
        request.sign = signRequest({
            type: "remove_distributor",
            distributor: distributor,
            asset: asset,
            timestamp: request.timestamp
        }, proxySecret);
        return fetch_api('/remove-distributor', {
            method: "POST",
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify(request)
        }).then(r => responseParse(r, false));
    }

    exchangeAPI.getConvertValues = function () {
        return fetch_api('/get-convert-values').then(responseParse);
    }

    exchangeAPI.convertToBTC = function (amount, floID, sinkID, privKey) {
        return new Promise((resolve, reject) => {
            if (!floCrypto.verifyPrivKey(privKey, floID))
                return reject(ExchangeError(ExchangeError.BAD_REQUEST_CODE, "Invalid Private Key", errorCode.INVALID_PRIVATE_KEY));
            if (!floGlobals.currency)
                return reject(ExchangeError(ExchangeError.BAD_REQUEST_CODE, "Currency is not defined in floGlobals", errorCode.MISSING_PARAMETER));
            
            floTokenAPI.sendToken(privKey, amount, sinkID, '(convert to BTC)', floGlobals.currency).then(txid => {
                let request = {
                    floID: floID,
                    txid: txid,
                    coin: "BTC",
                    amount: amount,
                    timestamp: Date.now()
                };
                request.pubKey = floCrypto.getPubKeyHex(privKey);
                request.sign = signRequest({
                    type: "convert_to",
                    coin: request.coin,
                    amount: amount,
                    txid: txid,
                    timestamp: request.timestamp
                }, privKey);
                fetch_api('/convert-to', {
                    method: "POST",
                    headers: { 'Content-Type': 'application/json' },
                    body: JSON.stringify(request)
                }).then(r => responseParse(r, false)).then(resolve).catch(reject);
            }).catch(reject);
        });
    }

    exchangeAPI.convertFromBTC = function (quantity, floID, sinkID, privKey, fee = null) {
        return new Promise((resolve, reject) => {
            if (!floCrypto.verifyPrivKey(privKey, floID))
                return reject(ExchangeError(ExchangeError.BAD_REQUEST_CODE, "Invalid Private Key", errorCode.INVALID_PRIVATE_KEY));
            
            let btc_id = btcOperator.convert.legacy2bech(floID);
            let btc_sink = btcOperator.convert.legacy2bech(sinkID);
            btcOperator.createSignedTx(btc_id, privKey, btc_sink, quantity, fee).then(result => {
                let request = {
                    floID: floID,
                    txid: btcOperator.transactionID(result.transaction),
                    tx_hex: result.transaction.serialize(),
                    coin: "BTC",
                    quantity: quantity,
                    timestamp: Date.now()
                };
                request.pubKey = floCrypto.getPubKeyHex(privKey);
                request.sign = signRequest({
                    type: "convert_from",
                    coin: request.coin,
                    quantity: quantity,
                    txid: request.txid,
                    timestamp: request.timestamp
                }, privKey);
                fetch_api('/convert-from', {
                    method: "POST",
                    headers: { 'Content-Type': 'application/json' },
                    body: JSON.stringify(request)
                }).then(r => responseParse(r, false)).then(resolve).catch(reject);
            }).catch(reject);
        });
    }

    exchangeAPI.depositConvertFundCurrency = function (amount, floID, sinkID, privKey) {
        return new Promise((resolve, reject) => {
            if (!floCrypto.verifyPrivKey(privKey, floID))
                return reject(ExchangeError(ExchangeError.BAD_REQUEST_CODE, "Invalid Private Key", errorCode.INVALID_PRIVATE_KEY));
            if (floID !== DEFAULT.marketID)
                return reject(ExchangeError(ExchangeError.BAD_REQUEST_CODE, "Access Denied", errorCode.ACCESS_DENIED));
            if (!floGlobals.currency)
                return reject(ExchangeError(ExchangeError.BAD_REQUEST_CODE, "Currency is not defined in floGlobals", errorCode.MISSING_PARAMETER));
            
            floTokenAPI.sendToken(privKey, amount, sinkID, '(add convert fund)', floGlobals.currency).then(txid => {
                let request = {
                    floID: floID,
                    txid: txid,
                    coin: "BTC",
                    timestamp: Date.now()
                };
                request.pubKey = floCrypto.getPubKeyHex(privKey);
                request.sign = signRequest({
                    type: "deposit_convert_currency_fund",
                    coin: request.coin,
                    txid: txid,
                    timestamp: request.timestamp
                }, privKey);
                fetch_api('/deposit-convert-currency-fund', {
                    method: "POST",
                    headers: { 'Content-Type': 'application/json' },
                    body: JSON.stringify(request)
                }).then(r => responseParse(r, false)).then(resolve).catch(reject);
            }).catch(reject);
        });
    }

    exchangeAPI.depositConvertFundBTC = function (quantity, floID, sinkID, privKey) {
        return new Promise((resolve, reject) => {
            if (!floCrypto.verifyPrivKey(privKey, floID))
                return reject(ExchangeError(ExchangeError.BAD_REQUEST_CODE, "Invalid Private Key", errorCode.INVALID_PRIVATE_KEY));
            if (floID !== DEFAULT.marketID)
                return reject(ExchangeError(ExchangeError.BAD_REQUEST_CODE, "Access Denied", errorCode.ACCESS_DENIED));
            
            let btc_id = btcOperator.convert.legacy2bech(floID);
            let btc_sink = btcOperator.convert.legacy2bech(sinkID);
            btcOperator.sendTx(btc_id, privKey, btc_sink, quantity, null).then(txid => {
                let request = {
                    floID: floID,
                    txid: txid,
                    coin: "BTC",
                    timestamp: Date.now()
                };
                request.pubKey = floCrypto.getPubKeyHex(privKey);
                request.sign = signRequest({
                    type: "deposit_convert_coin_fund",
                    coin: request.coin,
                    txid: txid,
                    timestamp: request.timestamp
                }, privKey);
                fetch_api('/deposit-convert-coin-fund', {
                    method: "POST",
                    headers: { 'Content-Type': 'application/json' },
                    body: JSON.stringify(request)
                }).then(r => responseParse(r, false)).then(resolve).catch(reject);
            }).catch(reject);
        });
    }

    exchangeAPI.withdrawConvertFundCurrency = function (amount, floID, privKey) {
        if (!floCrypto.verifyPrivKey(privKey, floID))
            return Promise.reject(ExchangeError(ExchangeError.BAD_REQUEST_CODE, "Invalid Private Key", errorCode.INVALID_PRIVATE_KEY));
        if (floID !== DEFAULT.marketID)
            return Promise.reject(ExchangeError(ExchangeError.BAD_REQUEST_CODE, "Access Denied", errorCode.ACCESS_DENIED));
        let request = {
            floID: floID,
            amount: amount,
            coin: "BTC",
            timestamp: Date.now()
        };
        request.pubKey = floCrypto.getPubKeyHex(privKey);
        request.sign = signRequest({
            type: "withdraw_convert_currency_fund",
            coin: request.coin,
            amount: amount,
            timestamp: request.timestamp
        }, privKey);
        return fetch_api('/withdraw-convert-currency-fund', {
            method: "POST",
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify(request)
        }).then(r => responseParse(r, false));
    }

    exchangeAPI.withdrawConvertFundCoin = function (quantity, floID, privKey) {
        if (!floCrypto.verifyPrivKey(privKey, floID))
            return Promise.reject(ExchangeError(ExchangeError.BAD_REQUEST_CODE, "Invalid Private Key", errorCode.INVALID_PRIVATE_KEY));
        if (floID !== DEFAULT.marketID)
            return Promise.reject(ExchangeError(ExchangeError.BAD_REQUEST_CODE, "Access Denied", errorCode.ACCESS_DENIED));
        let request = {
            floID: floID,
            quantity: quantity,
            coin: "BTC",
            timestamp: Date.now()
        };
        request.pubKey = floCrypto.getPubKeyHex(privKey);
        request.sign = signRequest({
            type: "withdraw_convert_coin_fund",
            coin: request.coin,
            quantity: quantity,
            timestamp: request.timestamp
        }, privKey);
        return fetch_api('/withdraw-convert-coin-fund', {
            method: "POST",
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify(request)
        }).then(r => responseParse(r, false));
    }

    exchangeAPI.closeBlockchainBond = function (bond_id, floID, privKey) {
        if (!floCrypto.verifyPrivKey(privKey, floID))
            return Promise.reject(ExchangeError(ExchangeError.BAD_REQUEST_CODE, "Invalid Private Key", errorCode.INVALID_PRIVATE_KEY));
        let request = {
            floID: floID,
            bond_id: bond_id,
            timestamp: Date.now()
        };
        request.pubKey = floCrypto.getPubKeyHex(privKey);
        request.sign = signRequest({
            type: "close_blockchain_bond",
            bond_id: request.bond_id,
            timestamp: request.timestamp
        }, privKey);
        return fetch_api('/close-blockchain-bonds', {
            method: "POST",
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify(request)
        }).then(responseParse);
    }

    exchangeAPI.checkBlockchainBond = function (prior_time, floID, proxySecret) {
        let request = {
            floID: floID,
            prior_time,
            timestamp: Date.now()
        };
        if (floCrypto.getFloID(proxySecret) === floID)
            request.pubKey = floCrypto.getPubKeyHex(proxySecret);
        request.sign = signRequest({
            type: "check_blockchain_bond",
            prior_time,
            timestamp: request.timestamp
        }, proxySecret);
        return fetch_api('/check-blockchain-bond', {
            method: "POST",
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify(request)
        }).then(responseParse);
    }

    exchangeAPI.checkBobsFund = function (prior_time, floID, proxySecret) {
        let request = {
            floID: floID,
            prior_time,
            timestamp: Date.now()
        };
        if (floCrypto.getFloID(proxySecret) === floID)
            request.pubKey = floCrypto.getPubKeyHex(proxySecret);
        request.sign = signRequest({
            type: "check_bobs_fund",
            prior_time,
            timestamp: request.timestamp
        }, proxySecret);
        return fetch_api('/check-bobs-fund', {
            method: "POST",
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify(request)
        }).then(responseParse);
    }

    exchangeAPI.closeBobsFundInvestment = function (fund_id, floID, privKey) {
        if (!floCrypto.verifyPrivKey(privKey, floID))
            return Promise.reject(ExchangeError(ExchangeError.BAD_REQUEST_CODE, "Invalid Private Key", errorCode.INVALID_PRIVATE_KEY));
        let request = {
            floID: floID,
            fund_id: fund_id,
            timestamp: Date.now()
        };
        request.pubKey = floCrypto.getPubKeyHex(privKey);
        request.sign = signRequest({
            type: "close_bobs_fund",
            fund_id: request.fund_id,
            timestamp: request.timestamp
        }, privKey);
        return fetch_api('/close-bobs-fund-investment', {
            method: "POST",
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify(request)
        }).then(responseParse);
    }

    exchangeAPI.generateSink = function (group, floID, privKey) {
        if (!floCrypto.verifyPrivKey(privKey, floID))
            return Promise.reject(ExchangeError(ExchangeError.BAD_REQUEST_CODE, "Invalid Private Key", errorCode.INVALID_PRIVATE_KEY));
        if (floID !== DEFAULT.marketID)
            return Promise.reject(ExchangeError(ExchangeError.BAD_REQUEST_CODE, "Access Denied", errorCode.ACCESS_DENIED));
        let request = {
            floID: floID,
            group: group,
            timestamp: Date.now()
        };
        request.pubKey = floCrypto.getPubKeyHex(privKey);
        request.sign = signRequest({
            type: "generate_sink",
            group: group,
            timestamp: request.timestamp
        }, privKey);
        return fetch_api('/generate-sink', {
            method: "POST",
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify(request)
        }).then(r => responseParse(r, false));
    }

    exchangeAPI.reshareSink = function (sinkID, floID, privKey) {
        if (!floCrypto.verifyPrivKey(privKey, floID))
            return Promise.reject(ExchangeError(ExchangeError.BAD_REQUEST_CODE, "Invalid Private Key", errorCode.INVALID_PRIVATE_KEY));
        if (floID !== DEFAULT.marketID)
            return Promise.reject(ExchangeError(ExchangeError.BAD_REQUEST_CODE, "Access Denied", errorCode.ACCESS_DENIED));
        let request = {
            floID: floID,
            id: sinkID,
            timestamp: Date.now()
        };
        request.pubKey = floCrypto.getPubKeyHex(privKey);
        request.sign = signRequest({
            type: "reshare_sink",
            id: sinkID,
            timestamp: request.timestamp
        }, privKey);
        return fetch_api('/reshare-sink', {
            method: "POST",
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify(request)
        }).then(r => responseParse(r, false));
    }

    exchangeAPI.discardSink = function (sinkID, floID, privKey) {
        if (!floCrypto.verifyPrivKey(privKey, floID))
            return Promise.reject(ExchangeError(ExchangeError.BAD_REQUEST_CODE, "Invalid Private Key", errorCode.INVALID_PRIVATE_KEY));
        if (floID !== DEFAULT.marketID)
            return Promise.reject(ExchangeError(ExchangeError.BAD_REQUEST_CODE, "Access Denied", errorCode.ACCESS_DENIED));
        let request = {
            floID: floID,
            id: sinkID,
            timestamp: Date.now()
        };
        request.pubKey = floCrypto.getPubKeyHex(privKey);
        request.sign = signRequest({
            type: "discard_sink",
            id: sinkID,
            timestamp: request.timestamp
        }, privKey);
        return fetch_api('/discard-sink', {
            method: "POST",
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify(request)
        }).then(r => responseParse(r, false));
    }

    const _l = key => DEFAULT.marketApp + '-' + key;

    function refreshDataFromBlockchain() {
        return new Promise((resolve, reject) => {
            let nodes, trusted = new Set(),
                assets, tags, lastTx;
            try {
                nodes = JSON.parse(g_localStorage.getItem(_l('nodes')));
                trusted = new Set((g_localStorage.getItem(_l('trusted')) || "").split(','));
                assets = new Set((g_localStorage.getItem(_l('assets')) || "").split(','));
                tags = new Set((g_localStorage.getItem(_l('tags')) || "").split(','));
                if (typeof nodes !== 'object' || nodes === null)
                    throw Error('nodes must be an object')
                else
                    lastTx = g_localStorage.getItem(_l('lastTx'));
            } catch (error) {
                nodes = {};
                trusted = new Set();
                assets = new Set();
                tags = new Set();
            }

            var query_options = {
                sentOnly: true,
                pattern: DEFAULT.marketApp
            };
            if (typeof lastTx == 'string' && /^[0-9a-f]{64}/i.test(lastTx))
                query_options.after = lastTx;
            else if (!isNaN(lastTx))
                query_options.ignoreOld = parseInt(lastTx);
            
            floBlockchainAPI.readData(DEFAULT.marketID, query_options).then(result => {
                result.data.reverse().forEach(data => {
                    var content = JSON.parse(data)[DEFAULT.marketApp];
                    if (content.Nodes) {
                        if (content.Nodes.remove)
                            for (let n of content.Nodes.remove)
                                delete nodes[n];
                        if (content.Nodes.add)
                            for (let n in content.Nodes.add)
                                nodes[n] = content.Nodes.add[n];
                        if (content.Nodes.update)
                            for (let n in content.Nodes.update)
                                nodes[n] = content.Nodes.update[n];
                    }
                    if (content.Trusted) {
                        if (content.Trusted.remove)
                            for (let id of content.Trusted.remove)
                                trusted.delete(id);
                        if (content.Trusted.add)
                            for (let id of content.Trusted.add)
                                trusted.add(id);
                    }
                    if (content.Assets) {
                        for (let a in content.Assets)
                            assets.add(a);
                    }
                    if (content.Tag) {
                        if (content.Tag.remove)
                            for (let t of content.Tag.remove)
                                tags.delete(t);
                        if (content.Tag.add)
                            for (let t in content.Tag.add)
                                tags.add(t);
                    }
                });
                g_localStorage.setItem(_l('lastTx'), result.lastItem);
                g_localStorage.setItem(_l('nodes'), JSON.stringify(nodes));
                g_localStorage.setItem(_l('trusted'), Array.from(trusted).join(","));
                g_localStorage.setItem(_l('assets'), Array.from(assets).join(","));
                g_localStorage.setItem(_l('tags'), Array.from(tags).join(","));
                nodeURL = nodes;
                nodeKBucket = new K_Bucket(DEFAULT.marketID, Object.keys(nodeURL));
                nodeList = nodeKBucket.order;
                resolve(nodes);
            }).catch(reject);
        });
    }

    exchangeAPI.init = function (service = serviceList.EXCHANGE) {
        return new Promise((resolve, reject) => {
            refreshDataFromBlockchain().then(nodes => {
                getSink(service)
                    .then(sinkID => { if(floCrypto.validateAddr(sinkID)) _sinkID = sinkID })
                    .catch(error => console.error("Unable to fetch sinkID", error))
                    .finally(_ => resolve(nodes))
            }).catch(reject)
        });
    }

    const config = exchangeAPI.config = {
        get trustedList() {
            return new Set((g_localStorage.getItem(_l('trusted')) || "").split(','));
        },
        get assetList() {
            return new Set((g_localStorage.getItem(_l('assets')) || "").split(','));
        },
        get tagList() {
            return new Set((g_localStorage.getItem(_l('tags')) || "").split(','));
        }
    }

    exchangeAPI.clearAllLocalData = function () {
        g_localStorage.removeItem(_l('nodes'));
        g_localStorage.removeItem(_l('trusted'));
        g_localStorage.removeItem(_l('assets'));
        g_localStorage.removeItem(_l('tags'));
        g_localStorage.removeItem(_l('lastTx'));
        g_localStorage.removeItem(_l('proxy_secret'));
        g_localStorage.removeItem(_l('user_ID'));
        g_location.reload();
    }

    var _userID, _publicKey, _privateKey, _sinkID;
    const proxy = exchangeAPI.proxy = {
        async lock() {
            if (!_privateKey)
                return notify("No proxy key found!", 'error');
            try {
                const pwd = await getPromptInput("Add password", 'This password applies to this browser only!', {
                    isPassword: true,
                    confirmText: "Add password"
                });
                if (!pwd)
                    notify("Password cannot be empty", 'error');
                else if (pwd.length < 4)
                    notify("Password minimum length is 4", 'error');
                else {
                    let tmp = Crypto.AES.encrypt(_privateKey, pwd);
                    g_localStorage.setItem(_l('proxy_secret'), "?" + tmp);
                    notify("Successfully locked with Password", 'success');
                }
            } catch (e) { /* User cancelled prompt */ }
        },
        clear() {
            g_localStorage.removeItem(_l('proxy_secret'));
            g_localStorage.removeItem(_l('user_ID'));
            _userID = null;
            _privateKey = null;
            _publicKey = null;
        },
        get sinkID() {
            return _sinkID;
        },
        set userID(id) {
            g_localStorage.setItem(_l('user_ID'), id);
            _userID = id;
        },
        get userID() {
            if (_userID)
                return _userID;
            else {
                let id = g_localStorage.getItem(_l('user_ID'));
                return id ? _userID = id : undefined;
            }
        },
        get user() {
            return this.userID;
        },
        set secret(key) {
            g_localStorage.setItem(_l('proxy_secret'), key);
            _privateKey = key;
            _publicKey = floCrypto.getPubKeyHex(key);
        },
        get secret() {
            return new Promise((resolve, reject) => {
                if (_privateKey)
                    return resolve(_privateKey);

                const Reject = reason => {
                    notify(reason, 'error');
                    reject(reason);
                }
                const setValues = priv => {
                    try {
                        _privateKey = priv;
                        _publicKey = floCrypto.getPubKeyHex(priv);
                        resolve(_privateKey);
                    } catch (error) {
                        Reject("Unable to fetch Proxy secret");
                    }
                };
                let tmp = g_localStorage.getItem(_l('proxy_secret'));
                if (typeof tmp !== "string")
                    Reject("Unable to fetch Proxy secret");
                else if (tmp.startsWith("?")) {
                    getPromptInput("Enter password", '', {
                        isPassword: true
                    }).then(pwd => {
                        if (!pwd)
                            return Reject("Password Required for making transactions");
                        try {
                            tmp = Crypto.AES.decrypt(tmp.substring(1), pwd);
                            setValues(tmp);
                        } catch (error) {
                            Reject("Incorrect Password! Password Required for making transactions");
                        }
                    }).catch(_ => Reject("Password Required for making transactions"));
                } else
                    setValues(tmp);
            })
        }
    }

})('object' === typeof module ? module.exports : window.floExchangeAPI = {});

